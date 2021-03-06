/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Theory of topological groups.

-/
import order.filter.pointwise
import group_theory.quotient_group
import topology.algebra.monoid
import topology.homeomorph

open classical set filter topological_space
open_locale classical topological_space filter

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section topological_group

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class topological_add_group (α : Type u) [topological_space α] [add_group α]
  extends has_continuous_add α : Prop :=
(continuous_neg : continuous (λa:α, -a))

/-- A topological group is a group in which the multiplication and inversion operations are
continuous. -/
@[to_additive]
class topological_group (α : Type*) [topological_space α] [group α]
  extends has_continuous_mul α : Prop :=
(continuous_inv : continuous (λa:α, a⁻¹))

variables [topological_space α] [group α]

@[to_additive]
lemma continuous_inv [topological_group α] : continuous (λx:α, x⁻¹) :=
topological_group.continuous_inv

@[to_additive, continuity]
lemma continuous.inv [topological_group α] [topological_space β] {f : β → α}
  (hf : continuous f) : continuous (λx, (f x)⁻¹) :=
continuous_inv.comp hf

attribute [continuity] continuous.neg

@[to_additive]
lemma continuous_on_inv [topological_group α] {s : set α} : continuous_on (λx:α, x⁻¹) s :=
continuous_inv.continuous_on

@[to_additive]
lemma continuous_on.inv [topological_group α] [topological_space β] {f : β → α} {s : set β}
  (hf : continuous_on f s) : continuous_on (λx, (f x)⁻¹) s :=
continuous_inv.comp_continuous_on hf

@[to_additive]
lemma tendsto_inv {α : Type*} [group α]
  [topological_space α] [topological_group α] (a : α) :
  tendsto (λ x, x⁻¹) (nhds a) (nhds (a⁻¹)) :=
continuous_inv.tendsto a

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive]
lemma filter.tendsto.inv [topological_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (𝓝 a)) : tendsto (λx, (f x)⁻¹) x (𝓝 a⁻¹) :=
tendsto.comp (continuous_iff_continuous_at.mp topological_group.continuous_inv a) hf

@[to_additive]
lemma continuous_at.inv [topological_group α] [topological_space β] {f : β → α} {x : β}
  (hf : continuous_at f x) : continuous_at (λx, (f x)⁻¹) x :=
hf.inv

@[to_additive]
lemma continuous_within_at.inv [topological_group α] [topological_space β] {f : β → α}
  {s : set β} {x : β} (hf : continuous_within_at f s x) :
  continuous_within_at (λx, (f x)⁻¹) s x :=
hf.inv

@[to_additive]
instance [topological_group α] [topological_space β] [group β] [topological_group β] :
  topological_group (α × β) :=
{ continuous_inv := continuous_fst.inv.prod_mk continuous_snd.inv }

attribute [instance] prod.topological_add_group

/-- Multiplication from the left in a topological group as a homeomorphism.-/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_left [topological_group α] (a : α) : α ≃ₜ α :=
{ continuous_to_fun  := continuous_const.mul continuous_id,
  continuous_inv_fun := continuous_const.mul continuous_id,
  .. equiv.mul_left a }

@[to_additive]
lemma is_open_map_mul_left [topological_group α] (a : α) : is_open_map (λ x, a * x) :=
(homeomorph.mul_left a).is_open_map

@[to_additive]
lemma is_closed_map_mul_left [topological_group α] (a : α) : is_closed_map (λ x, a * x) :=
(homeomorph.mul_left a).is_closed_map

/-- Multiplication from the right in a topological group as a homeomorphism.-/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_right
  {α : Type*} [topological_space α] [group α] [topological_group α] (a : α) :
  α ≃ₜ α :=
{ continuous_to_fun  := continuous_id.mul continuous_const,
  continuous_inv_fun := continuous_id.mul continuous_const,
  .. equiv.mul_right a }

@[to_additive]
lemma is_open_map_mul_right [topological_group α] (a : α) : is_open_map (λ x, x * a) :=
(homeomorph.mul_right a).is_open_map

@[to_additive]
lemma is_closed_map_mul_right [topological_group α] (a : α) : is_closed_map (λ x, x * a) :=
(homeomorph.mul_right a).is_closed_map

/-- Inversion in a topological group as a homeomorphism.-/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def homeomorph.inv (α : Type*) [topological_space α] [group α] [topological_group α] :
  α ≃ₜ α :=
{ continuous_to_fun  := continuous_inv,
  continuous_inv_fun := continuous_inv,
  .. equiv.inv α }

@[to_additive exists_nhds_half]
lemma exists_nhds_split [topological_group α] {s : set α} (hs : s ∈ 𝓝 (1 : α)) :
  ∃ V ∈ 𝓝 (1 : α), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:α×α, a.1 * a.2) ⁻¹' s) ∈ 𝓝 ((1, 1) : α × α) :=
    tendsto_mul (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

@[to_additive exists_nhds_half_neg]
lemma exists_nhds_split_inv [topological_group α] {s : set α} (hs : s ∈ 𝓝 (1 : α)) :
  ∃ V ∈ 𝓝 (1 : α), ∀ (v ∈ V) (w ∈ V), v * w⁻¹ ∈ s :=
begin
  have : tendsto (λa:α×α, a.1 * (a.2)⁻¹) (𝓝 (1:α) ×ᶠ 𝓝 (1:α)) (𝓝 1),
  { simpa using (@tendsto_fst α α (𝓝 1) (𝓝 1)).mul tendsto_snd.inv },
  have : ((λa:α×α, a.1 * (a.2)⁻¹) ⁻¹' s) ∈ 𝓝 (1:α) ×ᶠ 𝓝 (1:α) :=
    this (by simpa using hs),
  rcases mem_prod_self_iff.1 this with ⟨V, H, H'⟩,
  exact ⟨V, H, prod_subset_iff.1 H'⟩
end

@[to_additive exists_nhds_quarter]
lemma exists_nhds_split4 [topological_group α] {u : set α} (hu : u ∈ 𝓝 (1 : α)) :
  ∃ V ∈ 𝓝 (1 : α), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_split hu with ⟨W, W_nhd, h⟩,
  rcases exists_nhds_split W_nhd with ⟨V, V_nhd, h'⟩,
  existsi [V, V_nhd],
  intros v w s t v_in w_in s_in t_in,
  simpa [mul_assoc] using h _ _ (h' v w v_in w_in) (h' s t s_in t_in)
end

section
variable (α)
@[to_additive]
lemma nhds_one_symm [topological_group α] : comap (λr:α, r⁻¹) (𝓝 (1 : α)) = 𝓝 (1 : α) :=
begin
  have lim : tendsto (λr:α, r⁻¹) (𝓝 1) (𝓝 1),
  { simpa using (@tendsto_id α (𝓝 1)).inv },
  refine comap_eq_of_inverse _ _ lim lim,
  { funext x, simp },
end
end

@[to_additive]
lemma nhds_translation_mul_inv [topological_group α] (x : α) :
  comap (λy:α, y * x⁻¹) (𝓝 1) = 𝓝 x :=
begin
  refine comap_eq_of_inverse (λy:α, y * x) _ _ _,
  { funext x; simp },
  { suffices : tendsto (λy:α, y * x⁻¹) (𝓝 x) (𝓝 (x * x⁻¹)), { simpa },
    exact tendsto_id.mul tendsto_const_nhds },
  { suffices : tendsto (λy:α, y * x) (𝓝 1) (𝓝 (1 * x)), { simpa },
    exact tendsto_id.mul tendsto_const_nhds }
end

@[to_additive]
lemma topological_group.ext {G : Type*} [group G] {t t' : topological_space G}
  (tg : @topological_group G t _) (tg' : @topological_group G t' _)
  (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
eq_of_nhds_eq_nhds $ λ x, by
  rw [← @nhds_translation_mul_inv G t _ _ x , ← @nhds_translation_mul_inv G t' _ _ x , ← h]
end topological_group

section quotient_topological_group
variables [topological_space α] [group α] [topological_group α] (N : subgroup α) (n : N.normal)

@[to_additive]
instance {α : Type u} [group α] [topological_space α] (N : subgroup α) :
  topological_space (quotient_group.quotient N) :=
by dunfold quotient_group.quotient; apply_instance

open quotient_group
@[to_additive]
lemma quotient_group_saturate {α : Type u} [group α] (N : subgroup α) (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, y*x.1) '' s) :=
begin
  ext x,
  simp only [mem_preimage, mem_image, mem_Union, quotient_group.eq],
  split,
  { exact assume ⟨a, a_in, h⟩, ⟨⟨_, h⟩, a, a_in, mul_inv_cancel_left _ _⟩ },
  { exact assume ⟨⟨i, hi⟩, a, ha, eq⟩,
      ⟨a, ha, by { simp only [eq.symm, (mul_assoc _ _ _).symm, inv_mul_cancel_left], exact hi }⟩ }
end

@[to_additive]
lemma quotient_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_map_mul_right n s s_op
end

@[to_additive]
instance topological_group_quotient (n : N.normal) : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.to_quotient_map,
      { exact is_open_map.prod (quotient_group.open_coe N) (quotient_group.open_coe N) },
      { exact (continuous_quot_mk.comp continuous_fst).prod_mk
              (continuous_quot_mk.comp continuous_snd) },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        exact ⟨(x, y), rfl⟩ } },
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), a⁻¹)),
    exact continuous_quot_mk.comp continuous_inv
  end }

attribute [instance] topological_add_group_quotient

end quotient_topological_group


section topological_add_group
variables [topological_space α] [add_group α]

@[continuity] lemma continuous.sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x - g x) :=
by simp [sub_eq_add_neg]; exact hf.add hg.neg

lemma continuous_sub [topological_add_group α] : continuous (λp:α×α, p.1 - p.2) :=
continuous_fst.sub continuous_snd

lemma continuous_on.sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α} {s : set β}
  (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (λx, f x - g x) s :=
continuous_sub.comp_continuous_on (hf.prod hg)

lemma filter.tendsto.sub [topological_add_group α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) : tendsto (λx, f x - g x) x (𝓝 (a - b)) :=
by simp [sub_eq_add_neg]; exact hf.add hg.neg

lemma nhds_translation [topological_add_group α] (x : α) : comap (λy:α, y - x) (𝓝 0) = 𝓝 x :=
nhds_translation_add_neg x

end topological_add_group

/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (α : Type u) extends add_comm_group α :=
(Z [] : filter α)
(zero_Z : pure 0 ≤ Z)
(sub_Z : tendsto (λp:α×α, p.1 - p.2) (Z ×ᶠ Z) Z)

namespace add_group_with_zero_nhd
variables (α) [add_group_with_zero_nhd α]

local notation `Z` := add_group_with_zero_nhd.Z

@[priority 100] -- see Note [lower instance priority]
instance : topological_space α :=
topological_space.mk_of_nhds $ λa, map (λx, x + a) (Z α)

variables {α}

lemma neg_Z : tendsto (λa:α, - a) (Z α) (Z α) :=
have tendsto (λa, (0:α)) (Z α) (Z α),
  by refine le_trans (assume h, _) zero_Z; simp [univ_mem_sets'] {contextual := tt},
have tendsto (λa:α, 0 - a) (Z α) (Z α), from
  sub_Z.comp (tendsto.prod_mk this tendsto_id),
by simpa

lemma add_Z : tendsto (λp:α×α, p.1 + p.2) (Z α ×ᶠ Z α) (Z α) :=
suffices tendsto (λp:α×α, p.1 - -p.2) (Z α ×ᶠ Z α) (Z α),
  by simpa [sub_eq_add_neg],
sub_Z.comp (tendsto.prod_mk tendsto_fst (neg_Z.comp tendsto_snd))

lemma exists_Z_half {s : set α} (hs : s ∈ Z α) : ∃ V ∈ Z α, ∀ (v ∈ V) (w ∈ V), v + w ∈ s :=
begin
  have : ((λa:α×α, a.1 + a.2) ⁻¹' s) ∈ Z α ×ᶠ Z α := add_Z (by simpa using hs),
  rcases mem_prod_self_iff.1 this with ⟨V, H, H'⟩,
  exact ⟨V, H, prod_subset_iff.1 H'⟩
end

lemma nhds_eq (a : α) : 𝓝 a = map (λx, x + a) (Z α) :=
topological_space.nhds_mk_of_nhds _ _
  (assume a, calc pure a = map (λx, x + a) (pure 0) : by simp
    ... ≤ _ : map_mono zero_Z)
  (assume b s hs,
    let ⟨t, ht, eqt⟩ := exists_Z_half hs in
    have t0 : (0:α) ∈ t, by simpa using zero_Z ht,
    begin
      refine ⟨(λx:α, x + b) '' t, image_mem_map ht, _, _⟩,
      { refine set.image_subset_iff.2 (assume b hbt, _),
        simpa using eqt 0 t0 b hbt },
      { rintros _ ⟨c, hb, rfl⟩,
        refine (Z α).sets_of_superset ht (assume x hxt, _),
        simpa [add_assoc] using eqt _ hxt _ hb }
    end)

lemma nhds_zero_eq_Z : 𝓝 0 = Z α := by simp [nhds_eq]; exact filter.map_id

@[priority 100] -- see Note [lower instance priority]
instance : has_continuous_add α :=
⟨ continuous_iff_continuous_at.2 $ assume ⟨a, b⟩,
  begin
    rw [continuous_at, nhds_prod_eq, nhds_eq, nhds_eq, nhds_eq, filter.prod_map_map_eq,
      tendsto_map'_iff],
    suffices :  tendsto ((λx:α, (a + b) + x) ∘ (λp:α×α,p.1 + p.2)) (Z α ×ᶠ Z α)
      (map (λx:α, (a + b) + x) (Z α)),
    { simpa [(∘), add_comm, add_left_comm] },
    exact tendsto_map.comp add_Z
  end ⟩

@[priority 100] -- see Note [lower instance priority]
instance : topological_add_group α :=
⟨continuous_iff_continuous_at.2 $ assume a,
  begin
    rw [continuous_at, nhds_eq, nhds_eq, tendsto_map'_iff],
    suffices : tendsto ((λx:α, x - a) ∘ (λx:α, -x)) (Z α) (map (λx:α, x - a) (Z α)),
    { simpa [(∘), add_comm, sub_eq_add_neg] using this },
    exact tendsto_map.comp neg_Z
  end⟩

end add_group_with_zero_nhd

section filter_mul

section
variables [topological_space α] [group α] [topological_group α]

@[to_additive]
lemma is_open_mul_left {s t : set α} : is_open t → is_open (s * t) := λ ht,
begin
  have : ∀a, is_open ((λ (x : α), a * x) '' t),
    assume a, apply is_open_map_mul_left, exact ht,
  rw ← Union_mul_left_image,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

@[to_additive]
lemma is_open_mul_right {s t : set α} : is_open s → is_open (s * t) := λ hs,
begin
  have : ∀a, is_open ((λ (x : α), x * a) '' s),
    assume a, apply is_open_map_mul_right, exact hs,
  rw ← Union_mul_right_image,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

variables (α)

lemma topological_group.t1_space (h : @is_closed α _ {1}) : t1_space α :=
⟨assume x, by { convert is_closed_map_mul_right x _ h, simp }⟩

lemma topological_group.regular_space [t1_space α] : regular_space α :=
⟨assume s a hs ha,
 let f := λ p : α × α, p.1 * (p.2)⁻¹ in
 have hf : continuous f :=
   continuous_mul.comp (continuous_fst.prod_mk (continuous_inv.comp continuous_snd)),
 -- a ∈ -s implies f (a, 1) ∈ -s, and so (a, 1) ∈ f⁻¹' (-s);
 -- and so can find t₁ t₂ open such that a ∈ t₁ × t₂ ⊆ f⁻¹' (-s)
 let ⟨t₁, t₂, ht₁, ht₂, a_mem_t₁, one_mem_t₂, t_subset⟩ :=
   is_open_prod_iff.1 (hf _ (is_open_compl_iff.2 hs)) a (1:α) (by simpa [f]) in
 begin
   use s * t₂,
   use is_open_mul_left ht₂,
   use λ x hx, ⟨x, 1, hx, one_mem_t₂, mul_one _⟩,
   apply inf_principal_eq_bot,
   rw mem_nhds_sets_iff,
   refine ⟨t₁, _, ht₁, a_mem_t₁⟩,
   rintros x hx ⟨y, z, hy, hz, yz⟩,
   have : x * z⁻¹ ∈ sᶜ := (prod_subset_iff.1 t_subset) x hx z hz,
   have : x * z⁻¹ ∈ s, rw ← yz, simpa,
   contradiction
 end⟩

local attribute [instance] topological_group.regular_space

lemma topological_group.t2_space [t1_space α] : t2_space α := regular_space.t2_space α

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variables [topological_space α] [group α] [topological_group α]
/-- Given a open neighborhood `U` of `1` there is a open neighborhood `V` of `1`
  such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
lemma one_open_separated_mul {U : set α} (h1U : is_open U) (h2U : (1 : α) ∈ U) :
  ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ V * V ⊆ U :=
begin
  rcases exists_nhds_square (continuous_mul U h1U) (by simp only [mem_preimage, one_mul, h2U] :
    ((1 : α), (1 : α)) ∈ (λ p : α × α, p.1 * p.2) ⁻¹' U) with ⟨V, h1V, h2V, h3V⟩,
  refine ⟨V, h1V, h2V, _⟩,
  rwa [← image_subset_iff, image_mul_prod] at h3V
end

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `0`
  such that `K + V ⊆ U`."]
lemma compact_open_separated_mul {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ K * V ⊆ U :=
begin
  let W : α → set α := λ x, (λ y, x * y) ⁻¹' U,
  have h1W : ∀ x, is_open (W x) := λ x, continuous_mul_left x U hU,
  have h2W : ∀ x ∈ K, (1 : α) ∈ W x := λ x hx, by simp only [mem_preimage, mul_one, hKU hx],
  choose V hV using λ x : K, one_open_separated_mul (h1W x) (h2W x.1 x.2),
  let X : K → set α := λ x, (λ y, (x : α)⁻¹ * y) ⁻¹' (V x),
  cases hK.elim_finite_subcover X (λ x, continuous_mul_left x⁻¹ (V x) (hV x).1) _ with t ht, swap,
  { intros x hx, rw [mem_Union], use ⟨x, hx⟩, rw [mem_preimage], convert (hV _).2.1,
    simp only [mul_left_inv, subtype.coe_mk] },
  refine ⟨⋂ x ∈ t, V x, is_open_bInter (finite_mem_finset _) (λ x hx, (hV x).1), _, _⟩,
  { simp only [mem_Inter], intros x hx, exact (hV x).2.1 },
  rintro _ ⟨x, y, hx, hy, rfl⟩, simp only [mem_Inter] at hy,
  have := ht hx, simp only [mem_Union, mem_preimage] at this, rcases this with ⟨z, h1z, h2z⟩,
  have : (z : α)⁻¹ * x * y ∈ W z := (hV z).2.2 (mul_mem_mul h2z (hy z h1z)),
  rw [mem_preimage] at this, convert this using 1, simp only [mul_assoc, mul_inv_cancel_left]
end

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive "A compact set is covered by finitely many left additive translates of a set
  with non-empty interior."]
lemma compact_covered_by_mul_left_translates {K V : set α} (hK : is_compact K)
  (hV : (interior V).nonempty) : ∃ t : finset α, K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V :=
begin
  cases hV with g₀ hg₀,
  rcases is_compact.elim_finite_subcover hK (λ x : α, interior $ (λ h, x * h) ⁻¹' V) _ _ with ⟨t, ht⟩,
  { refine ⟨t, subset.trans ht _⟩,
    apply Union_subset_Union, intro g, apply Union_subset_Union, intro hg, apply interior_subset },
  { intro g, apply is_open_interior },
  { intros g hg, rw [mem_Union], use g₀ * g⁻¹,
    apply preimage_interior_subset_interior_preimage, exact continuous_const.mul continuous_id,
    rwa [mem_preimage, inv_mul_cancel_right] }
end

end

section
variables [topological_space α] [comm_group α] [topological_group α]

@[to_additive]
lemma nhds_mul (x y : α) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
filter_eq $ set.ext $ assume s,
begin
  rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x*y)],
  split,
  { rintros ⟨t, ht, ts⟩,
    rcases exists_nhds_split ht with ⟨V, V_mem, h⟩,
    refine ⟨(λa, a * x⁻¹) ⁻¹' V, (λa, a * y⁻¹) ⁻¹' V,
            ⟨V, V_mem, subset.refl _⟩, ⟨V, V_mem, subset.refl _⟩, _⟩,
    rintros a ⟨v, w, v_mem, w_mem, rfl⟩,
    apply ts,
    simpa [mul_comm, mul_assoc, mul_left_comm] using h (v * x⁻¹) (w * y⁻¹) v_mem w_mem },
  { rintros ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩,
    refine ⟨b ∩ d, inter_mem_sets hb hd, assume v, _⟩,
    simp only [preimage_subset_iff, mul_inv_rev, mem_preimage] at *,
    rintros ⟨vb, vd⟩,
    refine ac ⟨v * y⁻¹, y, _, _, _⟩,
    { rw ← mul_assoc _ _ _ at vb, exact ba _ vb },
    { apply dc y, rw mul_right_inv, exact mem_of_nhds hd },
    { simp only [inv_mul_cancel_right] } }
end

@[to_additive]
lemma nhds_is_mul_hom : is_mul_hom (λx:α, 𝓝 x) := ⟨λ_ _, nhds_mul _ _⟩

end

end filter_mul
