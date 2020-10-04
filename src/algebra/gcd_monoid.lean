/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

TODO: Provide a GCD monoid instance for `ℕ`, port GCD facts about nats
TODO: Generalize normalization monoids commutative (cancellative) monoids with or without zero
TODO: Generalize GCD monoid to not require normalization in all cases
-/
import algebra.associated
import data.nat.basic
import data.int.gcd

/-!

# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `comm_cancel_monoid_with_zero`s, including `integral_domain`s.

## Main Definitions

* `normalization_monoid`
* `gcd_monoid`

## Implementation Notes

* `normalization_monoid` is defined by assigning to each element a `norm_unit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `gcd_monoid` extends `normalization_monoid`, so the `gcd` and `lcm` are always normalized.
This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains, and monoids
without zero.

## TODO

* Provide a GCD monoid instance for `ℕ`, port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero
* Generalize GCD monoid to not require normalization in all cases


## Tags

divisibility, gcd, lcm, normalize

-/

variables {α : Type*}

set_option old_structure_cmd true



/-- Normalization monoid: multiplying with `norm_unit` gives a normal form for associated elements. -/
@[protect_proj] class normalization_monoid (α : Type*) [nontrivial α]
  [comm_cancel_monoid_with_zero α] :=
(norm_unit : α → units α)
(norm_unit_zero      : norm_unit 0 = 1)
(norm_unit_mul       : ∀{a b}, a ≠ 0 → b ≠ 0 → norm_unit (a * b) = norm_unit a * norm_unit b)
(norm_unit_coe_units : ∀(u : units α), norm_unit u = u⁻¹)

export normalization_monoid (norm_unit norm_unit_zero norm_unit_mul norm_unit_coe_units)

attribute [simp] norm_unit_coe_units norm_unit_zero norm_unit_mul

section normalization_monoid
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α]

@[simp] theorem norm_unit_one : norm_unit (1:α) = 1 :=
norm_unit_coe_units 1

/-- Chooses an element of each associate class, by multiplying by `norm_unit` -/
def normalize : α →* α :=
{ to_fun := λ x, x * norm_unit x,
  map_one' := by rw [norm_unit_one, units.coe_one, mul_one],
  map_mul' := λ x y,
  classical.by_cases (λ hx : x = 0, by rw [hx, zero_mul, zero_mul, zero_mul]) $ λ hx,
  classical.by_cases (λ hy : y = 0, by rw [hy, mul_zero, zero_mul, mul_zero]) $ λ hy,
  by simp only [norm_unit_mul hx hy, units.coe_mul]; simp only [mul_assoc, mul_left_comm y], }

theorem associated_normalize {x : α} : associated x (normalize x) :=
⟨_, rfl⟩

theorem normalize_associated {x : α} : associated (normalize x) x :=
associated_normalize.symm

lemma associates.mk_normalize {x : α} : associates.mk (normalize x) = associates.mk x :=
associates.mk_eq_mk_iff_associated.2 normalize_associated

@[simp] lemma normalize_apply {x : α} : normalize x = x * norm_unit x := rfl

@[simp] lemma normalize_zero : normalize (0 : α) = 0 := by simp

@[simp] lemma normalize_one : normalize (1 : α) = 1 := normalize.map_one

lemma normalize_coe_units (u : units α) : normalize (u : α) = 1 := by simp

lemma normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
⟨λ hx, (associated_zero_iff_eq_zero x).1 $ hx ▸ associated_normalize, by rintro rfl; exact normalize_zero⟩

lemma normalize_eq_one {x : α} : normalize x = 1 ↔ is_unit x :=
⟨λ hx, is_unit_iff_exists_inv.2 ⟨_, hx⟩, λ ⟨u, hu⟩, hu ▸ normalize_coe_units u⟩

@[simp] theorem norm_unit_mul_norm_unit (a : α) : norm_unit (a * norm_unit a) = 1 :=
classical.by_cases (assume : a = 0, by simp only [this, norm_unit_zero, zero_mul]) $
  assume h, by rw [norm_unit_mul h (units.ne_zero _), norm_unit_coe_units, mul_inv_eq_one]

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp

theorem normalize_eq_normalize {a b : α}
  (hab : a ∣ b) (hba : b ∣ a) : normalize a = normalize b :=
begin
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩,
  refine classical.by_cases (by rintro rfl; simp only [zero_mul]) (assume ha : a ≠ 0, _),
  suffices : a * ↑(norm_unit a) = a * ↑u * ↑(norm_unit a) * ↑u⁻¹,
    by simpa only [normalize_apply, mul_assoc, norm_unit_mul ha u.ne_zero, norm_unit_coe_units],
  calc a * ↑(norm_unit a) = a * ↑(norm_unit a) * ↑u * ↑u⁻¹:
      (units.mul_inv_cancel_right _ _).symm
    ... = a * ↑u * ↑(norm_unit a) * ↑u⁻¹ : by rw mul_right_comm a
end

lemma normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x :=
⟨λ h, ⟨units.dvd_mul_right.1 ⟨_, h.symm⟩, units.dvd_mul_right.1 ⟨_, h⟩⟩,
λ ⟨hxy, hyx⟩, normalize_eq_normalize hxy hyx⟩

theorem dvd_antisymm_of_normalize_eq {a b : α}
  (ha : normalize a = a) (hb : normalize b = b) (hab : a ∣ b) (hba : b ∣ a) :
  a = b :=
ha ▸ hb ▸ normalize_eq_normalize hab hba

--can be proven by simp
lemma dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
units.dvd_mul_right

--can be proven by simp
lemma normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
units.mul_right_dvd

end normalization_monoid

namespace associates
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α]

local attribute [instance] associated.setoid

/-- Maps an element of `associates` back to the normalized element of its associate class -/
protected def out : associates α → α :=
quotient.lift (normalize : α → α) $ λ a b ⟨u, hu⟩, hu ▸
normalize_eq_normalize ⟨_, rfl⟩ (units.mul_right_dvd.2 $ dvd_refl a)

lemma out_mk (a : α) : (associates.mk a).out = normalize a := rfl

@[simp] lemma out_one : (1 : associates α).out = 1 :=
normalize_one

lemma out_mul (a b : associates α) : (a * b).out = a.out * b.out :=
quotient.induction_on₂ a b $ assume a b,
by simp only [associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize.map_mul]

lemma dvd_out_iff (a : α) (b : associates α) : a ∣ b.out ↔ associates.mk a ≤ b :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

lemma out_dvd_iff (a : α) (b : associates α) : b.out ∣ a ↔ b ≤ associates.mk a :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

@[simp] lemma out_top : (⊤ : associates α).out = 0 :=
normalize_zero

@[simp] lemma normalize_out (a : associates α) : normalize a.out = a.out :=
quotient.induction_on a normalize_idem

end associates

/-- GCD monoid: a `comm_cancel_monoid_with_zero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
@[protect_proj] class gcd_monoid (α : Type*) [comm_cancel_monoid_with_zero α] [nontrivial α]
  extends normalization_monoid α :=
(gcd : α → α → α)
(lcm : α → α → α)
(gcd_dvd_left   : ∀a b, gcd a b ∣ a)
(gcd_dvd_right  : ∀a b, gcd a b ∣ b)
(dvd_gcd        : ∀{a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
(normalize_gcd  : ∀a b, normalize (gcd a b) = gcd a b)
(gcd_mul_lcm    : ∀a b, gcd a b * lcm a b = normalize (a * b))
(lcm_zero_left  : ∀a, lcm 0 a = 0)
(lcm_zero_right : ∀a, lcm a 0 = 0)

export gcd_monoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd  lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section gcd_monoid
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]

@[simp] theorem normalize_gcd : ∀a b:α, normalize (gcd a b) = gcd a b :=
gcd_monoid.normalize_gcd

@[simp] theorem gcd_mul_lcm : ∀a b:α, gcd a b * lcm a b = normalize (a * b) :=
gcd_monoid.gcd_mul_lcm

section gcd

theorem dvd_gcd_iff (a b c : α) : a ∣ gcd b c ↔ (a ∣ b ∧ a ∣ c) :=
iff.intro
  (assume h, ⟨dvd_trans h (gcd_dvd_left _ _), dvd_trans h (gcd_dvd_right _ _)⟩)
  (assume ⟨hab, hac⟩, dvd_gcd hab hac)

theorem gcd_comm (a b : α) : gcd a b = gcd b a :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (dvd_gcd
    (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
    (dvd_gcd (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
  (dvd_gcd
    (dvd_gcd (gcd_dvd_left m (gcd n k)) (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
    (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

instance : is_commutative α gcd := ⟨gcd_comm⟩
instance : is_associative α gcd := ⟨gcd_assoc⟩

theorem gcd_eq_normalize {a b c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) :
  gcd a b = normalize c :=
normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = normalize a :=
gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = normalize a :=
gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp] theorem gcd_eq_zero_iff (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume h, let ⟨ca, ha⟩ := gcd_dvd_left a b, ⟨cb, hb⟩ := gcd_dvd_right a b in
    by rw [h, zero_mul] at ha hb; exact ⟨ha, hb⟩)
  (assume ⟨ha, hb⟩, by rw [ha, hb, gcd_zero_left, normalize_zero])

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp] theorem gcd_one_right (a : α) : gcd a 1 = 1 :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

theorem gcd_dvd_gcd {a b c d: α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
dvd_gcd (dvd.trans (gcd_dvd_left _ _) hab) (dvd.trans (gcd_dvd_right _ _) hcd)

@[simp] theorem gcd_same (a : α) : gcd a a = normalize a :=
gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp] theorem gcd_mul_left (a b c : α) : gcd (a * b) (a * c) = normalize a * gcd b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, gcd_zero_left, normalize_zero]) $ assume ha : a ≠ 0,
suffices gcd (a * b) (a * c) = normalize (a * gcd b c),
  by simpa only [normalize.map_mul, normalize_gcd],
let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c) in
gcd_eq_normalize
  (eq.symm ▸ mul_dvd_mul_left a $ show d ∣ gcd b c, from
    dvd_gcd
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_left _ _)
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_right _ _))
  (dvd_gcd
    (mul_dvd_mul_left a $ gcd_dvd_left _ _)
    (mul_dvd_mul_left a $ gcd_dvd_right _ _))

@[simp] theorem gcd_mul_right (a b c : α) : gcd (b * a) (c * a) = gcd b c * normalize a :=
by simp only [mul_comm, gcd_mul_left]

theorem gcd_eq_left_iff (a b : α) (h : normalize a = a) : gcd a b = a ↔ a ∣ b :=
iff.intro (assume eq, eq ▸ gcd_dvd_right _ _) $
  assume hab, dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff (a b : α) (h : normalize b = b) : gcd a b = b ↔ b ∣ a :=
by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left (m n k : α) : gcd m n ∣ gcd (k * m) n :=
gcd_dvd_gcd (dvd_mul_left _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_right (m n k : α) : gcd m n ∣ gcd (m * k) n :=
gcd_dvd_gcd (dvd_mul_right _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_left_right (m n k : α) : gcd m n ∣ gcd m (k * n) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : α) : gcd m n ∣ gcd m (n * k) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_right _ _)

theorem gcd_eq_of_associated_left {m n : α} (h : associated m n) (k : α) : gcd m k = gcd n k :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (gcd_dvd_gcd (dvd_of_associated h) (dvd_refl _))
  (gcd_dvd_gcd (dvd_of_associated h.symm) (dvd_refl _))

theorem gcd_eq_of_associated_right {m n : α} (h : associated m n) (k : α) : gcd k m = gcd k n :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (gcd_dvd_gcd (dvd_refl _) (dvd_of_associated h))
  (gcd_dvd_gcd (dvd_refl _) (dvd_of_associated h.symm))

end gcd

section lcm

lemma lcm_dvd_iff {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=
classical.by_cases
  (assume : a = 0 ∨ b = 0, by rcases this with rfl | rfl;
    simp only [iff_def, lcm_zero_left, lcm_zero_right, zero_dvd_iff, dvd_zero,
      eq_self_iff_true, and_true, imp_true_iff] {contextual:=tt})
  (assume this : ¬ (a = 0 ∨ b = 0),
    let ⟨h1, h2⟩ := not_or_distrib.1 this in
    have h : gcd a b ≠ 0, from λ H, h1 ((gcd_eq_zero_iff _ _).1 H).1,
    by rw [← mul_dvd_mul_iff_left h, gcd_mul_lcm, normalize_dvd_iff, ← dvd_normalize_iff,
        normalize.map_mul, normalize_gcd, ← gcd_mul_right, dvd_gcd_iff,
        mul_comm b c, mul_dvd_mul_iff_left h1, mul_dvd_mul_iff_right h2, and_comm])

lemma dvd_lcm_left (a b : α) : a ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).1

lemma dvd_lcm_right (a b : α) : b ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).2

lemma lcm_dvd {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp] theorem lcm_eq_zero_iff (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
iff.intro
  (assume h : lcm a b = 0,
    have normalize (a * b) = 0,
      by rw [← gcd_mul_lcm _ _, h, mul_zero],
    by simpa only [normalize_eq_zero, mul_eq_zero, units.ne_zero, or_false])
  (by rintro (rfl | rfl); [apply lcm_zero_left, apply lcm_zero_right])

@[simp] lemma normalize_lcm (a b : α) : normalize (lcm a b) = lcm a b :=
classical.by_cases (assume : lcm a b = 0, by rw [this, normalize_zero]) $
  assume h_lcm : lcm a b ≠ 0,
  have h1 : gcd a b ≠ 0, from mt (by rw [gcd_eq_zero_iff, lcm_eq_zero_iff];
    rintros ⟨rfl, rfl⟩; left; refl) h_lcm,
  have h2 : normalize (gcd a b * lcm a b) = gcd a b * lcm a b,
    by rw [gcd_mul_lcm, normalize_idem],
  by simpa only [normalize.map_mul, normalize_gcd, one_mul, mul_right_inj' h1] using h2

theorem lcm_comm (a b : α) : lcm a b = lcm b a :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left _ _) (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_right _ _)))
    (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_right _ _)))
  (lcm_dvd
    (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance : is_commutative α lcm := ⟨lcm_comm⟩
instance : is_associative α lcm := ⟨lcm_assoc⟩

lemma lcm_eq_normalize {a b c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) :
  lcm a b = normalize c :=
normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
lcm_dvd (dvd.trans hab (dvd_lcm_left _ _)) (dvd.trans hcd (dvd_lcm_right _ _))

@[simp] theorem lcm_units_coe_left (u : units α) (a : α) : lcm ↑u a = normalize a :=
lcm_eq_normalize (lcm_dvd units.coe_dvd (dvd_refl _)) (dvd_lcm_right _ _)

@[simp] theorem lcm_units_coe_right (a : α) (u : units α) : lcm a ↑u = normalize a :=
(lcm_comm a u).trans $ lcm_units_coe_left _ _

@[simp] theorem lcm_one_left (a : α) : lcm 1 a = normalize a :=
lcm_units_coe_left 1 a

@[simp] theorem lcm_one_right (a : α) : lcm a 1 = normalize a :=
lcm_units_coe_right a 1

@[simp] theorem lcm_same (a : α) : lcm a a = normalize a :=
lcm_eq_normalize (lcm_dvd (dvd_refl _) (dvd_refl _)) (dvd_lcm_left _ _)

@[simp] theorem lcm_eq_one_iff (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
iff.intro
  (assume eq, eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩)
  (assume ⟨⟨c, hc⟩, ⟨d, hd⟩⟩,
    show lcm (units.mk_of_mul_eq_one a c hc.symm : α) (units.mk_of_mul_eq_one b d hd.symm) = 1,
      by rw [lcm_units_coe_left, normalize_coe_units])

@[simp] theorem lcm_mul_left (a b c : α) : lcm (a * b) (a * c) = normalize a * lcm b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, lcm_zero_left, normalize_zero]) $ assume ha : a ≠ 0,
suffices lcm (a * b) (a * c) = normalize (a * lcm b c),
  by simpa only [normalize.map_mul, normalize_lcm],
have a ∣ lcm (a * b) (a * c), from dvd.trans (dvd_mul_right _ _) (dvd_lcm_left _ _),
let ⟨d, eq⟩ := this in
lcm_eq_normalize
  (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
  (eq.symm ▸ (mul_dvd_mul_left a $ lcm_dvd
    ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_left _ _)
    ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_right _ _)))

@[simp] theorem lcm_mul_right (a b c : α) : lcm (b * a) (c * a) = lcm b c * normalize a :=
by simp only [mul_comm, lcm_mul_left]

theorem lcm_eq_left_iff (a b : α) (h : normalize a = a) : lcm a b = a ↔ b ∣ a :=
iff.intro (assume eq, eq ▸ dvd_lcm_right _ _) $
  assume hab, dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff (a b : α) (h : normalize b = b) : lcm a b = b ↔ a ∣ b :=
by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left (m n k : α) : lcm m n ∣ lcm (k * m) n :=
lcm_dvd_lcm (dvd_mul_left _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_right (m n k : α) : lcm m n ∣ lcm (m * k) n :=
lcm_dvd_lcm (dvd_mul_right _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_left_right (m n k : α) : lcm m n ∣ lcm m (k * n) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right (m n k : α) : lcm m n ∣ lcm m (n * k) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_right _ _)

theorem lcm_eq_of_associated_left {m n : α} (h : associated m n) (k : α) : lcm m k = lcm n k :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd_lcm (dvd_of_associated h) (dvd_refl _))
  (lcm_dvd_lcm (dvd_of_associated h.symm) (dvd_refl _))

theorem lcm_eq_of_associated_right {m n : α} (h : associated m n) (k : α) : lcm k m = lcm k n :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd_lcm (dvd_refl _) (dvd_of_associated h))
  (lcm_dvd_lcm (dvd_refl _) (dvd_of_associated h.symm))

end lcm

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
noncomputable def prod_dvd_and_dvd_of_dvd_prod {m n k : α} (H : k ∣ m * n) :
  { d : {m' // m' ∣ m} × {n' // n' ∣ n} // k = d.1 * d.2 } :=
begin
  by_cases h0 : gcd k m = 0,
  { rw gcd_eq_zero_iff at h0,
    rcases h0 with ⟨rfl, rfl⟩,
    refine ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, _⟩,
    simp },
  { let a := classical.some (gcd_dvd_left k m),
    refine ⟨⟨⟨gcd k m, gcd_dvd_right _ _⟩, ⟨a, _⟩⟩, classical.some_spec (gcd_dvd_left k m)⟩,
    suffices h : gcd k m * a ∣ gcd k m * n,
    { cases h with b hb,
      use b,
      rw mul_assoc at hb,
      apply mul_left_cancel' h0 hb },
    rw ← classical.some_spec (gcd_dvd_left k m),
    transitivity gcd k m * normalize n,
    { rw ← gcd_mul_right,
      exact dvd_gcd (dvd_mul_right _ _) H },
    { apply dvd.intro ↑(norm_unit n)⁻¹,
      rw [normalize_apply, mul_assoc, mul_assoc, ← units.coe_mul],
      simp } }
end

theorem gcd_mul_dvd_mul_gcd (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n :=
begin
  rcases (prod_dvd_and_dvd_of_dvd_prod $ gcd_dvd_right k (m * n)) with ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, h⟩,
  replace h : gcd k (m * n) = m' * n' := h,
  rw h,
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _,
  apply mul_dvd_mul,
    { have hm'k : m' ∣ k := dvd_trans (dvd_mul_right m' n') hm'n',
      exact dvd_gcd hm'k hm' },
    { have hn'k : n' ∣ k := dvd_trans (dvd_mul_left n' m') hm'n',
      exact dvd_gcd hn'k hn' }
end

namespace gcd_monoid
theorem prime_of_irreducible {x : α} (hi: irreducible x) : prime x :=
⟨hi.ne_zero, ⟨hi.1, λ a b h,
begin
  cases gcd_dvd_left x a with y hy,
  cases hi.2 _ _ hy with hu hu; cases hu with u hu,
  { right, transitivity (gcd (x * b) (a * b)), apply dvd_gcd (dvd_mul_right x b) h,
    rw gcd_mul_right, rw ← hu,
    apply dvd_of_associated, transitivity (normalize b), symmetry, use u, apply mul_comm,
    apply normalize_associated, },
  { left, rw [hy, ← hu],
    transitivity, {apply dvd_of_associated, symmetry, use u}, apply gcd_dvd_right, }
end ⟩⟩

theorem irreducible_iff_prime {p : α} : irreducible p ↔ prime p :=
⟨prime_of_irreducible, irreducible_of_prime⟩

end gcd_monoid
end gcd_monoid

namespace int

section normalization_monoid

instance : normalization_monoid ℤ :=
{ norm_unit      := λa:ℤ, if 0 ≤ a then 1 else -1,
  norm_unit_zero := if_pos (le_refl _),
  norm_unit_mul  := assume a b hna hnb,
  begin
    by_cases ha : 0 ≤ a; by_cases hb : 0 ≤ b; simp [ha, hb],
    exact if_pos (mul_nonneg ha hb),
    exact if_neg (assume h, hb $ nonneg_of_mul_nonneg_left h $ lt_of_le_of_ne ha hna.symm),
    exact if_neg (assume h, ha $ nonneg_of_mul_nonneg_right h $ lt_of_le_of_ne hb hnb.symm),
    exact if_pos (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (le_of_not_ge hb))
  end,
  norm_unit_coe_units := assume u, (units_eq_one_or u).elim
    (assume eq, eq.symm ▸ if_pos zero_le_one)
    (assume eq, eq.symm ▸ if_neg (not_le_of_gt $ show (-1:ℤ) < 0, by simp [@neg_lt ℤ _ 1 0])), }

lemma normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
show z * ↑(ite _ _ _) = z, by rw [if_pos h, units.coe_one, mul_one]

lemma normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
show z * ↑(ite _ _ _) = -z, by rw [if_neg (not_le_of_gt h), units.coe_neg, units.coe_one, mul_neg_one]

lemma normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
normalize_of_nonneg (coe_nat_le_coe_nat_of_le $ nat.zero_le n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.nat_abs : ℤ) = normalize z :=
begin
  by_cases 0 ≤ z,
  { simp [nat_abs_of_nonneg h, normalize_of_nonneg h] },
  { simp [of_nat_nat_abs_of_nonpos (le_of_not_ge h), normalize_of_neg (lt_of_not_ge h)] }
end

end normalization_monoid

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ := nat.lcm (nat_abs i) (nat_abs j)

theorem lcm_def (i j : ℤ) : lcm i j = nat.lcm (nat_abs i) (nat_abs j) := rfl

section gcd_monoid

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_left _ _

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
dvd_nat_abs.mp $ coe_nat_dvd.mpr $ nat.gcd_dvd_right _ _

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcd i j :=
nat_abs_dvd.1 $ coe_nat_dvd.2 $ nat.dvd_gcd (nat_abs_dvd_abs_iff.2 h1) (nat_abs_dvd_abs_iff.2 h2)

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = nat_abs (i * j) :=
by rw [int.gcd, int.lcm, nat.gcd_mul_lcm, nat_abs_mul]

instance : gcd_monoid ℤ :=
{ gcd            := λa b, int.gcd a b,
  lcm            := λa b, int.lcm a b,
  gcd_dvd_left   := assume a b, int.gcd_dvd_left _ _,
  gcd_dvd_right  := assume a b, int.gcd_dvd_right _ _,
  dvd_gcd        := assume a b c, dvd_gcd,
  normalize_gcd  := assume a b, normalize_coe_nat _,
  gcd_mul_lcm    := by intros; rw [← int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize],
  lcm_zero_left  := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_left _,
  lcm_zero_right := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_right _,
  .. int.normalization_monoid }

lemma coe_gcd (i j : ℤ) : ↑(int.gcd i j) = gcd_monoid.gcd i j := rfl
lemma coe_lcm (i j : ℤ) : ↑(int.lcm i j) = gcd_monoid.lcm i j := rfl

lemma nat_abs_gcd (i j : ℤ) : nat_abs (gcd_monoid.gcd i j) = int.gcd i j := rfl
lemma nat_abs_lcm (i j : ℤ) : nat_abs (gcd_monoid.lcm i j) = int.lcm i j := rfl

end gcd_monoid

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i := nat.gcd_comm _ _

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) := nat.gcd_assoc _ _ _

@[simp] theorem gcd_self (i : ℤ) : gcd i i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_left (i : ℤ) : gcd 0 i = nat_abs i := by simp [gcd]

@[simp] theorem gcd_zero_right (i : ℤ) : gcd i 0 = nat_abs i := by simp [gcd]

@[simp] theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 := nat.gcd_one_left _

@[simp] theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 := nat.gcd_one_right _

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = nat_abs i * gcd j k :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_normalize]

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * nat_abs j :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_gcd, coe_nat_abs_eq_normalize]

theorem gcd_pos_of_non_zero_left {i : ℤ} (j : ℤ) (i_non_zero : i ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_left (nat_abs j) (nat_abs_pos_of_ne_zero i_non_zero)

theorem gcd_pos_of_non_zero_right (i : ℤ) {j : ℤ} (j_non_zero : j ≠ 0) : 0 < gcd i j :=
nat.gcd_pos_of_pos_right (nat_abs i) (nat_abs_pos_of_ne_zero j_non_zero)

theorem gcd_eq_zero_iff {i j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
by rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_zero, coe_gcd, gcd_eq_zero_iff]

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
  gcd (i / k) (j / k) = gcd i j / nat_abs k :=
by rw [gcd, nat_abs_div i k H1, nat_abs_div j k H2];
exact nat.gcd_div (nat_abs_dvd_abs_iff.mpr H1) (nat_abs_dvd_abs_iff.mpr H2)

theorem gcd_div_gcd_div_gcd {i j : ℤ} (H : 0 < gcd i j) :
  gcd (i / gcd i j) (j / gcd i j) = 1 :=
begin
  rw [gcd_div (gcd_dvd_left i j) (gcd_dvd_right i j)],
  rw [nat_abs_of_nat, nat.div_self H]
end

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
int.coe_nat_dvd.1 $ dvd_gcd (dvd.trans (gcd_dvd_left i j) H) (gcd_dvd_right i j)

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
int.coe_nat_dvd.1 $ dvd_gcd (gcd_dvd_left j i) (dvd.trans (gcd_dvd_right j i) H)

theorem gcd_dvd_gcd_mul_left (i j k : ℤ) : gcd i j ∣ gcd (k * i) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (i j k : ℤ) : gcd i j ∣ gcd (i * k) j :=
gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (i j k : ℤ) : gcd i j ∣ gcd i (k * j) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (i j k : ℤ) : gcd i j ∣ gcd i (j * k) :=
gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {i j : ℤ} (H : i ∣ j) : gcd i j = nat_abs i :=
nat.dvd_antisymm (by unfold gcd; exact nat.gcd_dvd_left _ _)
                 (by unfold gcd; exact nat.dvd_gcd (dvd_refl _) (nat_abs_dvd_abs_iff.mpr H))

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcd i j = nat_abs j :=
by rw [gcd_comm, gcd_eq_left H]

theorem ne_zero_of_gcd {x y : ℤ}
  (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 :=
begin
  contrapose! hc,
  rw [hc.left, hc.right, gcd_zero_right, nat_abs_zero]
end

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (m' n' : ℤ), gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
⟨_, _, gcd_div_gcd_div_gcd H,
  (int.div_mul_cancel (gcd_dvd_left m n)).symm,
  (int.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
  ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
let ⟨m', n', h⟩ := exists_gcd_one H in ⟨_, m', n', H, h⟩

theorem pow_dvd_pow_iff {m n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n :=
begin
  refine ⟨λ h, _, λ h, pow_dvd_pow_of_dvd h _⟩,
  apply int.nat_abs_dvd_abs_iff.mp,
  apply (nat.pow_dvd_pow_iff k0).mp,
  rw [← int.nat_abs_pow, ← int.nat_abs_pow],
  exact int.nat_abs_dvd_abs_iff.mpr h
end

/- lcm -/

theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_comm]

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, lcm_assoc]

@[simp] theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm]

@[simp] theorem lcm_one_left (i : ℤ) : lcm 1 i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

@[simp] theorem lcm_one_right (i : ℤ) : lcm i 1 = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

@[simp] theorem lcm_self (i : ℤ) : lcm i i = nat_abs i :=
by simp [(int.coe_nat_eq_coe_nat_iff _ _).symm, coe_lcm, coe_nat_abs_eq_normalize]

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_left _ _

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j :=
by rw [coe_lcm]; exact dvd_lcm_right _ _

theorem lcm_dvd {i j k : ℤ}  : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k :=
by rw [coe_lcm]; exact lcm_dvd

end int

theorem irreducible_iff_nat_prime : ∀(a : ℕ), irreducible a ↔ nat.prime a
| 0 := by simp [nat.not_prime_zero]
| 1 := by simp [nat.prime, one_lt_two]
| (n + 2) :=
  have h₁ : ¬n + 2 = 1, from dec_trivial,
  begin
    simp [h₁, nat.prime, irreducible, (≥), nat.le_add_left 2 n, (∣)],
    refine forall_congr (assume a, forall_congr $ assume b, forall_congr $ assume hab, _),
    by_cases a = 1; simp [h],
    split,
    { assume hb, simpa [hb] using hab.symm },
    { assume ha, subst ha,
      have : n + 2 > 0, from dec_trivial,
      refine nat.eq_of_mul_eq_mul_left this _,
      rw [← hab, mul_one] }
  end

lemma nat.prime_iff_prime {p : ℕ} : p.prime ↔ _root_.prime (p : ℕ) :=
⟨λ hp, ⟨nat.pos_iff_ne_zero.1 hp.pos, mt is_unit_iff_dvd_one.1 hp.not_dvd_one,
    λ a b, hp.dvd_mul.1⟩,
  λ hp, ⟨nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp.1, λ h1, hp.2.1 $ h1.symm ▸ is_unit_one⟩,
    λ a h, let ⟨b, hab⟩ := h in
      (hp.2.2 a b (hab ▸ dvd_refl _)).elim
        (λ ha, or.inr (nat.dvd_antisymm h ha))
        (λ hb, or.inl (have hpb : p = b, from nat.dvd_antisymm hb
            (hab.symm ▸ dvd_mul_left _ _),
          (nat.mul_right_inj (show 0 < p, from
              nat.pos_of_ne_zero hp.1)).1 $
            by rw [hpb, mul_comm, ← hab, hpb, mul_one]))⟩⟩

lemma nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt is_unit_int.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff_prime.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt nat.is_unit_iff.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associates_int_equiv_nat : associates ℤ ≃ ℕ :=
begin
  refine ⟨λz, z.out.nat_abs, λn, associates.mk n, _, _⟩,
  { refine (assume a, quotient.induction_on' a $ assume a,
      associates.mk_eq_mk_iff_associated.2 $ associated.symm $ ⟨norm_unit a, _⟩),
    show normalize a = int.nat_abs (normalize a),
    rw [int.coe_nat_abs_eq_normalize, normalize_idem] },
  { intro n, dsimp, rw [associates.out_mk ↑n,
    ← int.coe_nat_abs_eq_normalize, int.nat_abs_of_nat, int.nat_abs_of_nat] }
end

lemma int.prime.dvd_mul {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : p ∣ m.nat_abs ∨ p ∣ n.nat_abs :=
begin
  apply (nat.prime.dvd_mul hp).mp,
  rw ← int.nat_abs_mul,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_mul' {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
begin
  rw [int.coe_nat_dvd_left, int.coe_nat_dvd_left],
  exact int.prime.dvd_mul hp h
end

lemma prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ int.nat_abs m :=
begin
  cases int.prime.dvd_mul hp h with hp2 hpp,
  { apply or.intro_left,
    exact le_antisymm (nat.le_of_dvd two_pos hp2) (nat.prime.two_le hp) },
  { apply or.intro_right,
    rw [pow_two, int.nat_abs_mul] at hpp,
    exact (or_self _).mp ((nat.prime.dvd_mul hp).mp hpp)}
end

section unique_unit

instance nat.unique_units : unique (units ℕ) :=
{ default := 1, uniq := nat.units_eq_one }

variables [comm_cancel_monoid_with_zero α] [unique (units α)]

lemma units_eq_one (u : units α) : u = 1 := subsingleton.elim u 1

variable [nontrivial α]

@[priority 100] -- see Note [lower instance priority]
instance normalization_monoid_of_unique_units : normalization_monoid α :=
{ norm_unit := λ x, 1,
  norm_unit_zero := rfl,
  norm_unit_mul := λ x y hx hy, (mul_one 1).symm,
  norm_unit_coe_units := λ u, subsingleton.elim _ _ }

@[simp] lemma norm_unit_eq_one (x : α) : norm_unit x = 1 := rfl

@[simp] lemma normalize_eq (x : α) : normalize x = x := mul_one x

end unique_unit

section integral_domain

variables [integral_domain α] [gcd_monoid α]

lemma gcd_eq_of_dvd_sub {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c :=
begin
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _);
  rw dvd_gcd_iff; refine ⟨gcd_dvd_left _ _, _⟩,
  { rcases h with ⟨d, hd⟩,
    rcases gcd_dvd_right a b with ⟨e, he⟩,
    rcases gcd_dvd_left a b with ⟨f, hf⟩,
    use e - f * d,
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel] },
  { rcases h with ⟨d, hd⟩,
    rcases gcd_dvd_right a c with ⟨e, he⟩,
    rcases gcd_dvd_left a c with ⟨f, hf⟩,
    use e + f * d,
    rw [mul_add, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_comm c b, add_sub_cancel] }
end

end integral_domain
