module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.CommSq
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.CategoryTheory.Filtered.SpanCocones

/-!
# Colimits over a preordered set: kernels, and the failure of exactness

Let `R` be a ring and let `I = {a, b, c}` be the partially ordered set with `a < b` and `a < c`
and no other strict inequalities. A system of `R`-modules over `I` is a triple `M_a, M_b, M_c`
of `R`-modules together with two `R`-module maps `μ_ab : M_a → M_b` and `μ_ac : M_a → M_c`, that
is, a span in the category of `R`-modules, and its colimit is the pushout

`M = colim_{i ∈ I} M_i = Coker(μ_ab ⊕ -μ_ac : M_a → M_b ⊕ M_c)`

with canonical maps `inl : M_b → M`, `inr : M_c → M` and `μ_ab ≫ inl = μ_ac ≫ inr : M_a → M`.
The kernels of the canonical maps out of the system can be read off from this description: the
kernel of `M_a → M` is `Ker(μ_ab) + Ker(μ_ac)` and the kernel of `M_b → M` is the image of
`Ker(μ_ac)` under `μ_ab`. So a class `μ_i(x_i)` can vanish in the colimit without `x_i` dying in
the system, and Lemma 00D7 fails over a preordered set that is not directed.

Exactness fails over `I` as well. The system `(0, B, C, 0, 0)` maps to `(A, B, C, μ_ab, μ_ac)` by
the morphism of systems `(0 → A, 𝟙 B, 𝟙 C)`, which is injective on each object, and its colimit
is the coproduct `L = B ⊔ C`; the induced map of colimits `ψ : L → M` kills `l (μ_ab x) - r (μ_ac
x)`, which is a nonzero element of the coproduct as soon as the span is nonzero. So the conclusion
of Lemma 00DB fails for systems over `I`.

Directedness is what is missing, and it is enough to have it componentwise: if every span in an
index category `J` is completed by a commutative square and every pair of parallel morphisms in
`J` is coequalized — the assumptions of Lemma 002X, which make `J` *pseudofiltered* — then `J` is
the disjoint union of its connected components, each filtered, so the colimit over `J` is the
coproduct of the colimits over the components. The first is exact by AB5, the second by AB4, and
AB4 follows from AB5, so colimits over `J` are exact.

## Main results

* `ModuleCat.ker_hom_comp_inl_and_ker_hom_inl_of_isPushout`: for a pushout square of `R`-modules,
  the kernel of the canonical map from the initial vertex is the sum of the kernels of the two
  maps of the span, and the kernel of `inl` is the image under `μ_ab` of the kernel of `μ_ac`.
* `ModuleCat.not_injective_hom_of_isColimit_binaryCofan_of_isPushout`: the canonical map from the
  coproduct `B ⊔ C` to the pushout of a span `B ← A → C` of `R`-modules is not injective as soon
  as one of the two maps of the span is nonzero.
* `CategoryTheory.hasExactColimitsOfShape_of_isPseudofiltered`: in an abelian category with exact
  filtered colimits, colimits over a pseudofiltered index category are exact.

## References

* [Stacks Project, Tag 00D8](https://stacks.math.columbia.edu/tag/00D8)
* [Stacks Project, Tag 00DC](https://stacks.math.columbia.edu/tag/00DC)
* [Stacks Project, Tag 04B0](https://stacks.math.columbia.edu/tag/04B0)
-/

@[expose] public section

universe w v u u₁ v₁

open CategoryTheory Limits

section Pushout

variable {R : Type u} [Ring R] {Ma Mb Mc M : ModuleCat.{v} R} {μab : Ma ⟶ Mb} {μac : Ma ⟶ Mc}
  {inl : Mb ⟶ M} {inr : Mc ⟶ M}

/-- The part of the image of `f ⊕ g = biprod.lift f g : A ⟶ B ⊞ C` lying in the summand `B` is the
image under `f` of the kernel of `g`. -/
private lemma comap_biprod_inl_range_biprod_lift {A B C : ModuleCat.{v} R} (f : A ⟶ B)
    (g : A ⟶ C) :
    (LinearMap.range (biprod.lift f g).hom).comap (biprod.inl : B ⟶ B ⊞ C).hom
      = Submodule.map f.hom (LinearMap.ker g.hom) := by
  ext b
  simp only [Submodule.mem_comap, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [← ModuleCat.comp_apply] using congrArg (biprod.snd : B ⊞ C ⟶ C).hom hx,
      by simpa [← ModuleCat.comp_apply] using congrArg (biprod.fst : B ⊞ C ⟶ B).hom hx⟩
  · rintro ⟨x, hgx, rfl⟩
    exact ⟨x, by simp [biprod.lift_eq, hgx]⟩

/-- For a pushout square of `R`-modules, `M_b ⊕ M_c → M` is a cokernel of `μ_ab ⊕ -μ_ac`: an
element of `M_b ⊕ M_c` dies in `M` exactly when it comes from `M_a`. -/
private lemma range_biprod_lift_eq_ker_biprod_desc (h : IsPushout μab μac inl inr) :
    LinearMap.range (biprod.lift μab (-μac) : Ma ⟶ Mb ⊞ Mc).hom
      = LinearMap.ker (biprod.desc inl inr : Mb ⊞ Mc ⟶ M).hom :=
  (ShortComplex.exact_of_g_is_cokernel h.shortComplex
    h.isColimitCokernelCofork).moduleCat_range_eq_ker

/-- For a pushout square of `R`-modules, the kernel of the canonical map `inl : M_b → M` is the
image under `μ_ab` of the kernel of `μ_ac`. -/
private lemma ker_hom_inl_of_isPushout (h : IsPushout μab μac inl inr) :
    LinearMap.ker inl.hom = Submodule.map μab.hom (LinearMap.ker μac.hom) := by
  rw [← biprod.inl_desc inl inr, ModuleCat.hom_comp, LinearMap.ker_comp,
    ← range_biprod_lift_eq_ker_biprod_desc h, comap_biprod_inl_range_biprod_lift,
    ModuleCat.hom_neg, LinearMap.ker_neg]

end Pushout

/-- Let `R` be a ring and let `M = colim M_i` be the colimit of a system of
`R`-modules over the poset `{a < b, a < c}`, that is, the pushout of a span
`M_b ← M_a → M_c` of `R`-modules, with canonical maps `inl : M_b → M` and `inr : M_c → M`. Then the
kernel of the canonical map `M_a → M` is `Ker(μ_ab) + Ker(μ_ac)`, and the kernel of `inl` is the
image of `Ker(μ_ac)` under `μ_ab`. -/
@[stacks 00D8 "The poset `{a < b, a < c}` is the span shape, so the colimit of a system over it is
a pushout in `ModuleCat R`, taken here abstractly rather than through the model
`Coker(μ_ab ⊕ -μ_ac)`; that the pushout is that cokernel is Mathlib's
`CategoryTheory.IsPushout.isColimitCokernelCofork`. The mirror `Ker(inr) = μ_ac(Ker(μ_ab))` is this
statement applied to `h.flip`."]
theorem ModuleCat.ker_hom_comp_inl_and_ker_hom_inl_of_isPushout {R : Type u} [Ring R]
    {Ma Mb Mc M : ModuleCat.{v} R} {μab : Ma ⟶ Mb} {μac : Ma ⟶ Mc} {inl : Mb ⟶ M} {inr : Mc ⟶ M}
    (h : IsPushout μab μac inl inr) :
    LinearMap.ker (μab ≫ inl).hom = LinearMap.ker μab.hom ⊔ LinearMap.ker μac.hom ∧
      LinearMap.ker inl.hom = Submodule.map μab.hom (LinearMap.ker μac.hom) := by
  refine ⟨?_, ker_hom_inl_of_isPushout h⟩
  rw [ModuleCat.hom_comp, LinearMap.ker_comp, ker_hom_inl_of_isPushout h,
    Submodule.comap_map_eq, sup_comm]

section ZeroMorphisms

variable {D : Type*} [Category D] [HasZeroMorphisms D] {X Y Z T : D}

/-- The two injections of a binary coproduct are disjoint: if `f ≫ l = g ≫ r` for the injections
`l`, `r` of a colimit binary cofan in a category with zero morphisms, then `f = 0` and `g = 0`. -/
private lemma eq_zero_and_eq_zero_of_comp_eq_comp_of_isColimit_binaryCofan {l : X ⟶ Z} {r : Y ⟶ Z}
    (hL : IsColimit (BinaryCofan.mk l r)) {f : T ⟶ X} {g : T ⟶ Y} (h : f ≫ l = g ≫ r) :
    f = 0 ∧ g = 0 := by
  obtain ⟨p, hlp, hrp⟩ : ∃ p : Z ⟶ X, l ≫ p = 𝟙 X ∧ r ≫ p = 0 :=
    ⟨_, (BinaryCofan.IsColimit.desc' hL (𝟙 X) 0).2⟩
  obtain ⟨q, hlq, hrq⟩ : ∃ q : Z ⟶ Y, l ≫ q = 0 ∧ r ≫ q = 𝟙 Y :=
    ⟨_, (BinaryCofan.IsColimit.desc' hL 0 (𝟙 Y)).2⟩
  exact ⟨by simpa [hlp, hrp] using h =≫ p, by simpa [hlq, hrq] using (h =≫ q).symm⟩

end ZeroMorphisms

/-- Taking colimits is not exact in general: let `R` be a ring, let `M` be the
colimit of a system `(A, B, C, μ_ab, μ_ac)` of `R`-modules over the poset `{a < b, a < c}`, that
is, the pushout of the span `B ← A → C`, and let `L` be the colimit `B ⊔ C` of the sub-system
`(0, B, C, 0, 0)`. If one of `μ_ab`, `μ_ac` is nonzero, then the induced map of colimits
`ψ : L → M` is not injective, even though the morphism of systems `(0 → A, 𝟙 B, 𝟙 C)` is
injective on each object. -/
@[stacks 00DC "The poset `{a < b, a < c}` is the span shape, so the colimit of a system over it is
a pushout in `ModuleCat R` and the colimit of the sub-system with apex the zero module is the
coproduct `B ⊔ C`; the morphism of systems `(0 → A, 𝟙 B, 𝟙 C)` is injective on each object, and
`ψ` is pinned by the two commuting squares of `Stacks 00DA`. Stated for an arbitrary nonzero span
over an arbitrary ring instead of the source's `(0, ℤ, ℤ, 0, 0) → (ℤ, ℤ, ℤ, 1, 1)`."]
theorem ModuleCat.not_injective_hom_of_isColimit_binaryCofan_of_isPushout {R : Type u}
    [Ring R] {A B C L M : ModuleCat.{v} R} {μab : A ⟶ B} {μac : A ⟶ C} {l : B ⟶ L} {r : C ⟶ L}
    {inl : B ⟶ M} {inr : C ⟶ M} {ψ : L ⟶ M} (hL : IsColimit (BinaryCofan.mk l r))
    (hM : IsPushout μab μac inl inr) (hl : l ≫ ψ = inl) (hr : r ≫ ψ = inr)
    (hμ : μab ≠ 0 ∨ μac ≠ 0) :
    ¬ Function.Injective ψ.hom := by
  intro hinj
  have : Mono ψ := (ModuleCat.mono_iff_injective ψ).2 hinj
  have key : μab ≫ l = μac ≫ r :=
    (cancel_mono ψ).1 <| by simpa only [Category.assoc, hl, hr] using hM.w
  obtain ⟨hab, hac⟩ := eq_zero_and_eq_zero_of_comp_eq_comp_of_isColimit_binaryCofan hL key
  exact hμ.elim (· hab) (· hac)

section Pseudofiltered


/-- A connected category in which every span can be completed to a commutative square and every
pair of parallel morphisms can be coequalized is filtered. -/
private lemma isFiltered_of_isPreconnected {K : Type u₁} [Category.{v₁} K] [IsPreconnected K]
    [Nonempty K]
    (hspan : ∀ ⦃x y z : K⦄ (a : x ⟶ y) (b : x ⟶ z), ∃ (t : K) (c : y ⟶ t) (d : z ⟶ t),
      a ≫ c = b ≫ d)
    (hpar : ∀ ⦃x y : K⦄ (a b : x ⟶ y), ∃ (z : K) (c : y ⟶ z), a ≫ c = b ≫ c) : IsFiltered K where
  cocone_objs x y := exists_cocone_of_zigzag hspan (isPreconnected_zigzag x y)
  cocone_maps := hpar

/-- The objects of a connected component are closed under zigzags. -/
private lemma objectProperty_of_zigzag {K : Type u₁} [Category.{v₁} K]
    {j : ConnectedComponents K} {x t : K} (hx : j.objectProperty x) (h : Zigzag x t) :
    j.objectProperty t :=
  (Quotient.sound' h.symm).trans hx

/-- Each connected component of a category in which every span can be completed to a commutative
square and every pair of parallel morphisms can be coequalized is filtered. -/
private lemma isFiltered_component {K : Type u₁} [Category.{v₁} K]
    (hspan : ∀ ⦃x y z : K⦄ (a : x ⟶ y) (b : x ⟶ z), ∃ (t : K) (c : y ⟶ t) (d : z ⟶ t),
      a ≫ c = b ≫ d)
    (hpar : ∀ ⦃x y : K⦄ (a b : x ⟶ y), ∃ (z : K) (c : y ⟶ z), a ≫ c = b ≫ c)
    (j : ConnectedComponents K) : IsFiltered j.Component := by
  refine isFiltered_of_isPreconnected (fun x y z a b ↦ ?_) (fun x y a b ↦ ?_)
  · obtain ⟨t, c, d, hcd⟩ := hspan a.hom b.hom
    exact ⟨⟨t, objectProperty_of_zigzag y.property (.of_hom c)⟩, ObjectProperty.homMk c,
      ObjectProperty.homMk d, ObjectProperty.hom_ext _ (by simpa using hcd)⟩
  · obtain ⟨t, c, hc⟩ := hpar a.hom b.hom
    exact ⟨⟨t, objectProperty_of_zigzag y.property (.of_hom c)⟩, ObjectProperty.homMk c,
      ObjectProperty.hom_ext _ (by simpa using hc)⟩

variable {C : Type u} [Category.{v} C]

/-- If `colim : (K ⥤ C) ⥤ C` preserves monomorphisms, then `colimMap φ` is a monomorphism as soon
as every component of `φ` is. -/
private lemma mono_colimMap {K : Type u₁} [Category.{v₁} K] [HasColimitsOfShape K C]
    [(colim (J := K) (C := C)).PreservesMonomorphisms] {X₁ X₂ : K ⥤ C} (φ : X₁ ⟶ X₂)
    (hφ : ∀ k, Mono (φ.app k)) : Mono (colimMap φ) :=
  MorphismProperty.colimMap (W := MorphismProperty.monomorphisms C) φ hφ

section Sigma

variable {I : Type w} {D : I → Type w} [∀ i, Category.{w} (D i)] {X₁ X₂ : (Σ i, D i) ⥤ C}

variable (X : (Σ i, D i) ⥤ C) [HasColimit X] [∀ i, HasColimit (Sigma.incl i ⋙ X)]
  [HasCoproduct fun i ↦ colimit (Sigma.incl i ⋙ X)]

/-- A colimit over a disjoint union of categories is the coproduct of the colimits over the
summands: the comparison maps `colimit.pre X (Sigma.incl i)` assemble into an isomorphism
`∐ i, colimit (Sigma.incl i ⋙ X) ≅ colimit X`. -/
@[simps hom]
private noncomputable def sigmaColimitIso :
    (∐ fun i ↦ colimit (Sigma.incl i ⋙ X)) ≅ colimit X where
  hom := Limits.Sigma.desc fun i ↦ colimit.pre X (Sigma.incl i)
  inv := colimit.desc X (Cocone.mk _
    { app := fun p ↦ colimit.ι (Sigma.incl p.1 ⋙ X) p.2 ≫
        Sigma.ι (fun i ↦ colimit (Sigma.incl i ⋙ X)) p.1
      naturality := by
        rintro ⟨i, x⟩ ⟨-, y⟩ ⟨f⟩
        simpa using colimit.w_assoc (Sigma.incl i ⋙ X) f
          (Sigma.ι (fun i ↦ colimit (Sigma.incl i ⋙ X)) i) })
  hom_inv_id := by
    ext i x
    simp only [Sigma.ι_comp_desc_assoc, colimit.ι_pre_assoc, colimit.ι_desc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext ⟨i, x⟩
    simp only [colimit.ι_desc_assoc, Category.comp_id]
    exact (Category.assoc ..).trans <| (whisker_eq (colimit.ι (Sigma.incl i ⋙ X) x)
      (Sigma.ι_comp_desc _ i)).trans (colimit.ι_pre X (Sigma.incl i) x)

variable [∀ i, HasColimit (Sigma.incl i ⋙ X₁)] [∀ i, HasColimit (Sigma.incl i ⋙ X₂)]
  [HasCoproduct fun i ↦ colimit (Sigma.incl i ⋙ X₁)]
  [HasCoproduct fun i ↦ colimit (Sigma.incl i ⋙ X₂)] [HasColimit X₁] [HasColimit X₂]

/-- `sigmaColimitIso` is natural: under it, `colimMap φ` becomes the coproduct of the maps induced
on the colimits over the summands. -/
private lemma sigmaMap_comp_sigmaColimitIso_hom (φ : X₁ ⟶ X₂) :
    (Limits.Sigma.map fun i ↦ colimMap (Functor.whiskerLeft (Sigma.incl i) φ)) ≫
      (sigmaColimitIso X₂).hom = (sigmaColimitIso X₁).hom ≫ colimMap φ := by
  ext i x
  simp only [sigmaColimitIso_hom, Sigma.ι_map_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
    ι_colimMap_assoc, colimit.ι_pre, colimit.ι_pre_assoc, ι_colimMap, Functor.whiskerLeft_app]

/-- Taking the colimit over a disjoint union of categories preserves monomorphisms as soon as
taking it over each summand and over the discrete category of the index set does. -/
private lemma preservesMonomorphisms_colim_sigma [HasPullbacks C] [HasColimitsOfSize.{w, w} C]
    [∀ i, (colim (J := D i) (C := C)).PreservesMonomorphisms]
    [(colim (J := Discrete I) (C := C)).PreservesMonomorphisms] :
    (colim (J := Σ i, D i) (C := C)).PreservesMonomorphisms where
  preserves {X₁ X₂} φ hφ := by
    have happ := (NatTrans.mono_iff_mono_app φ).1 hφ
    have : Mono (Limits.Sigma.map fun i ↦ colimMap (Functor.whiskerLeft (Sigma.incl i) φ)) :=
      mono_colimMap (K := Discrete I) _ fun k ↦ mono_colimMap _ fun _ ↦ happ _
    have key : colimMap φ = (sigmaColimitIso X₁).inv ≫
        (Limits.Sigma.map fun i ↦ colimMap (Functor.whiskerLeft (Sigma.incl i) φ)) ≫
          (sigmaColimitIso X₂).hom := by
      rw [sigmaMap_comp_sigmaColimitIso_hom φ, Iso.inv_hom_id_assoc]
    rw [colim_map, key]
    infer_instance

/-- Colimits over a disjoint union of filtered categories are exact in an abelian category with
exact filtered colimits. -/
private lemma hasExactColimitsOfShape_sigma [Abelian C] [HasColimitsOfSize.{w, w} C]
    [AB5OfSize.{w, w} C] [∀ i, IsFiltered (D i)] : HasExactColimitsOfShape (Σ i, D i) C := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have : AB4OfSize.{w} C := AB4.of_AB5 C
  have : (colim (J := Σ i, D i) (C := C)).PreservesMonomorphisms :=
    preservesMonomorphisms_colim_sigma
  exact hasExactColimitsOfShape_of_preservesMono C _

end Sigma

end Pseudofiltered

/-- Let `J` be an index category satisfying the assumptions of Stacks 002X: every span
`y ← x → z` is completed by some commutative square, and every pair of parallel morphisms
`a b : x ⟶ y` is coequalized by some `c : y ⟶ z`. Then taking colimits of diagrams over `J` in an
abelian category with exact filtered colimits is exact. -/
@[stacks 04B0 "Stated as `HasExactColimitsOfShape J C`, i.e. `colim : (J ⥤ C) ⥤ C` preserves
finite limits, which for a left adjoint is exactness and is the form of `Stacks 00DB` the source
asks for. The assumptions of `Stacks 002X` are spelled out because Mathlib has no predicate for
a pseudofiltered category. Stated for an arbitrary abelian category with colimits of size `w`
whose filtered colimits are exact, instead of the source's abelian groups, since the source's
proof uses only that; AB4 is derived from AB5 rather than assumed."]
theorem CategoryTheory.hasExactColimitsOfShape_of_isPseudofiltered {C : Type u}
    [Category.{v} C] [Abelian C] [Limits.HasColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    {J : Type w} [Category.{w} J]
    (hspan : ∀ ⦃x y z : J⦄ (a : x ⟶ y) (b : x ⟶ z), ∃ (t : J) (c : y ⟶ t) (d : z ⟶ t),
      a ≫ c = b ≫ d)
    (hpar : ∀ ⦃x y : J⦄ (a b : x ⟶ y), ∃ (z : J) (c : y ⟶ z), a ≫ c = b ≫ c) :
    HasExactColimitsOfShape J C := by
  have : ∀ j : ConnectedComponents J, IsFiltered j.Component :=
    isFiltered_component hspan hpar
  have : HasExactColimitsOfShape (Decomposed J) C := hasExactColimitsOfShape_sigma
  exact HasExactColimitsOfShape.of_domain_equivalence C decomposedEquiv

end
