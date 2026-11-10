module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NoetherianComponentEnvelope
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoofUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional

/-!
# Representing a morphism of perfect objects after an envelope

Let `X` be a scheme locally of finite type over the base of chapter 42 of the Stacks Project
whose irreducible components are quasi-compact, and let `φ : E ⟶ F` be a morphism of perfect
objects of `D(𝒪_X)`. Then there is an envelope `f : Y ⟶ X` such that `Lf^*φ` is represented by
a morphism of locally bounded complexes of finite locally free `𝒪_Y`-modules. This is the step
"condition (3) implies condition (1)" of the proof of [Stacks, Tag 0F9F].

The proof is the source's. The envelope is the one of the proof of clause (3) of
[Stacks, Tag 0GUE]: `Y` is a disjoint union of Noetherian schemes `Y_i` with the resolution
property. On each `Y_i` the restriction of `Lf^*φ` is represented by a map of bounded complexes
of finite locally free modules ([Stacks, Tag 0F8F] and [Stacks, Tag 0F8G]), and these maps are
glued along the decomposition of `Y` into the `Y_i`.

## Main results

* `DerivedCategory.exists_quasiIso_homotopy_of_Q_map_eq`: two maps of complexes with the same
  image in the derived category become homotopic after composition with a quasi-isomorphism.
* `Stacks.Chow.ClopenGlueing.Q_map_piMap_pushforward_eq`: on a decomposition into open and
  closed subschemes, the product of pushforwards respects equality in the derived categories.
* `Stacks.Chow.ClopenGlueing.exists_iso_Q_pi_pushforward_comm_of_hom`: glueing a map of
  complexes, identified on each piece with a map of complexes in the derived category, along
  such a decomposition.
* `exists_boundedFiniteLocallyFree_hom_iso_of_isNoetherian`, in the namespace
  `Stacks.Perfect.BoundedLocallyFreeComplexes`: on a Noetherian scheme with the resolution
  property, a morphism of perfect objects is represented by a map of bounded complexes of finite
  locally free modules.
* `Stacks.Chow.exists_envelope_mapPresentation_of_isCompact_irreducibleComponents`: the
  statement above.
* `Stacks.Chow.exists_envelope_mapPresentation_of_compactSpace`: the case of quasi-compact `X`.

## Implementation notes

The glueing of morphisms is where the work is. Write `Γ(Pᵢ) = ∏ᵢ jᵢ_* Pᵢ` for the product of
the pushforwards of complexes `Pᵢ` on the pieces `Uᵢ`. Since the pieces are open and closed,
`Γ` carries a family of quasi-isomorphisms to a quasi-isomorphism, and a complex `A` on `Y` is
quasi-isomorphic to `Γ(A|_{Uᵢ})` through the units of the adjunctions `(-)|_{Uᵢ} ⊣ jᵢ_*`,
naturally in `A`. A morphism of `D(𝒪_Y)` is a left fraction `Q(g) ≫ Q(s)⁻¹` of maps of
complexes, so families of morphisms of the `D(𝒪_{Uᵢ})` are glued by `Γ` once one knows that `Γ`
respects equality in the derived categories: if `Q(gᵢ) = Q(hᵢ)` for every `i`, then
`Q(Γ gᵢ) = Q(Γ hᵢ)`. That is not formal, as an infinite product of localization functors need
not be a localization functor. It holds here because `Q(gᵢ) = Q(hᵢ)` means that
`gᵢ ≫ tᵢ` and `hᵢ ≫ tᵢ` are homotopic for some quasi-isomorphism `tᵢ`, and homotopies, unlike
equalities in the derived category, are carried through products and pushforwards.

The homotopies on the pieces are assembled by `Stacks.DerivedProducts.homotopyPiOfComponents`,
which asks for products only, so the index set, the set of irreducible components of `X`, may
be uncountable.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

-- The standard model of the derived category is the one every derived-pullback statement used
-- below is stated at. The priority beats the locally small model: that one is a global
-- instance, so without it the statements here would be about an unrelated model.
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Homological algebra -/

/-- Two maps of cochain complexes with the same image in the derived category become homotopic
after composition with a suitable quasi-isomorphism: this is the left calculus of fractions of
the quasi-isomorphisms of the homotopy category. -/
theorem DerivedCategory.exists_quasiIso_homotopy_of_Q_map_eq {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] {X Y : CochainComplex C ℤ} {g h : X ⟶ Y}
    (H : DerivedCategory.Q.map g = DerivedCategory.Q.map h) :
    ∃ (Z : CochainComplex C ℤ) (t : Y ⟶ Z) (_ : QuasiIso t),
      Nonempty (Homotopy (g ≫ t) (h ≫ t)) := by
  have H' : DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map g) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map h) := by
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app Y),
      DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality, H]
  obtain ⟨Z, s, hs, fac⟩ := (MorphismProperty.map_eq_iff_postcomp DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _).1 H'
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  refine ⟨Z, t, (HomotopyCategory.quotient_map_mem_quasiIso_iff t).1 hs, ⟨?_⟩⟩
  apply HomotopyCategory.homotopyOfEq
  rw [Functor.map_comp, Functor.map_comp, fac]

/-- A diagram chase with left fractions. Let `F : X₀ ⟶ Y₀` be identified with `Rf` by
isomorphisms `ηA, ηB`, and let `Rf` be identified with `Al` by the left fractions `S⁻¹ ∘ G` and
`S'⁻¹ ∘ G'`, in the sense that the two equalities `S ≫ Cc = Al ≫ S' ≫ R` and
`Rf ≫ G' ≫ R = G ≫ Cc` hold for some `Cc` and some monomorphism `R`. Then `F` is identified
with `Al` by isomorphisms. -/
private theorem exists_iso_comp_hom_eq_of_fractions {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ Z : C} (F : X₀ ⟶ Y₀) (ηA : X₀ ⟶ X₁) (ηB : Y₀ ⟶ Y₁)
    (Rf : X₁ ⟶ Y₁) (G : X₁ ⟶ X₃) (S : X₂ ⟶ X₃) (G' : Y₁ ⟶ Y₃) (S' : Y₂ ⟶ Y₃) (Al : X₂ ⟶ Y₂)
    (Cc : X₃ ⟶ Z) (R : Y₃ ⟶ Z) [hηA : IsIso ηA] [hηB : IsIso ηB] [hG : IsIso G] [hS : IsIso S]
    [hG' : IsIso G'] [hS' : IsIso S'] [hR : Mono R] (hnat : F ≫ ηB = ηA ≫ Rf)
    (G1 : S ≫ Cc = Al ≫ S' ≫ R) (G2 : Rf ≫ G' ≫ R = G ≫ Cc) :
    ∃ (E : X₀ ≅ X₂) (E' : Y₀ ≅ Y₂), F ≫ E'.hom = E.hom ≫ Al := by
  refine ⟨asIso ηA ≪≫ asIso G ≪≫ (asIso S).symm, asIso ηB ≪≫ asIso G' ≪≫ (asIso S').symm, ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [reassoc_of% hnat]
  congr 1
  rw [← cancel_mono S', ← cancel_mono R]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [G2, ← G1, IsIso.inv_hom_id_assoc]

/-- Transport of a left fraction `g ≫ s⁻¹` representing `eA.hom ≫ φ ≫ eB₀.inv` along the
isomorphism `eB₀`: `g` is identified with `φ`. -/
private theorem exists_iso_comp_hom_eq {C : Type*} [Category C] {X Y Y₀ K L : C}
    (eA : X ≅ K) (eB₀ : Y₀ ≅ L) (φ : K ⟶ L) (g : X ⟶ Y) (s : Y₀ ⟶ Y) [hs : IsIso s]
    (h : eA.hom ≫ φ ≫ eB₀.inv = g ≫ inv s) :
    ∃ eB : Y ≅ L, g ≫ eB.hom = eA.hom ≫ φ := by
  refine ⟨(asIso s).symm ≪≫ eB₀, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc, ← h]
  simp

/-- If `g` is identified with `β` by `E₀, E₀'` and with `φ` by `eA, eB`, then `β` is
identified with `φ` by the composite isomorphisms. -/
private theorem comp_symm_trans_hom_eq {C : Type*} [Category C] {A B P P' K L : C}
    (g : A ⟶ B) (β : P ⟶ P') (φ : K ⟶ L) (E₀ : A ≅ P) (E₀' : B ≅ P') (eA : A ≅ K)
    (eB : B ≅ L) (hc : g ≫ E₀'.hom = E₀.hom ≫ β) (hg : g ≫ eB.hom = eA.hom ≫ φ) :
    β ≫ (E₀'.symm ≪≫ eB).hom = (E₀.symm ≪≫ eA).hom ≫ φ := by
  have h : E₀.inv ≫ g = β ≫ E₀'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc, ← hg,
    reassoc_of% h]

/-- Rewriting `x = a ≫ inv b` as `a = x ≫ b`. -/
private theorem eq_comp_of_eq_comp_inv {C : Type*} [Category C] {X Y Z : C} {x : X ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} [IsIso b] (h : x = a ≫ inv b) : a = x ≫ b :=
  ((IsIso.eq_comp_inv _).1 h).symm

/-! ### Glueing morphisms along a clopen decomposition -/

namespace Stacks.Chow.ClopenGlueing

open Stacks.Cohomology.HigherDirectImage RingedSpaceModuleAdjunction

variable {Y : Scheme.{u}}

local notation "ρ[" U "]" => moduleRestriction Y.toRingedSpace U
local notation "ψ[" U "]" => modulePushforward (openSubspaceInclusion Y.toRingedSpace U)
local notation "ρC[" V "]" => Functor.mapHomologicalComplex (ρ[V]) (ComplexShape.up ℤ)
local notation "ψC[" V "]" => Functor.mapHomologicalComplex (ψ[V]) (ComplexShape.up ℤ)
local notation "adj[" V "]" => restrictionAdjunctionComplex V

variable {I : Type u} (U : I → Y.Opens)

/-- The product of pushforwards of a family of maps of complexes that are isomorphisms in the
derived categories of the pieces is an isomorphism in `D(𝒪_Y)`. -/
private theorem isIso_Q_map_piMap_pushforward (hU : IsClopenDecomposition U)
    {P C : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    (x : ∀ k, P k ⟶ C k) (hx : ∀ k, IsIso (DerivedCategory.Q.map (x k))) :
    IsIso (DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (x k))) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_piMap_pushforward U hU x
    fun k => (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (hx k))

/-- **Glueing respects equality in the derived category.** If two families of maps of
complexes on the pieces of a clopen decomposition agree in the derived categories of the
pieces, the products of their pushforwards agree in `D(𝒪_Y)`. -/
theorem Q_map_piMap_pushforward_eq (hU : IsClopenDecomposition U)
    {P C : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    (g h : ∀ k, P k ⟶ C k)
    (H : ∀ k, DerivedCategory.Q.map (g k) = DerivedCategory.Q.map (h k)) :
    DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (g k)) =
      DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (h k)) := by
  choose Z t ht Ht using fun k => DerivedCategory.exists_quasiIso_homotopy_of_Q_map_eq (H k)
  have : IsIso (DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (t k))) :=
    isIso_Q_map_piMap_pushforward U hU t fun k =>
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (ht k)
  have : Mono (DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (t k))) :=
    IsIso.mono_of_iso _
  rw [← cancel_mono (DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (t k))),
    ← Functor.map_comp, ← Functor.map_comp]
  refine DerivedCategory.Q_map_eq_of_homotopy _
    (Stacks.DerivedProducts.homotopyPiOfComponents _ _ _ _ fun k => ?_)
  have e : ∀ x : ∀ k, P k ⟶ C k,
      (Limits.Pi.map (fun k => (ψC[U k]).map (x k)) ≫
        Limits.Pi.map fun k => (ψC[U k]).map (t k)) ≫ Pi.π _ k =
      Pi.π _ k ≫ (ψC[U k]).map (x k ≫ t k) := fun x => by
    simp [Functor.map_comp]
  exact (Homotopy.ofEq (e g)).trans
    ((((ψ[U k]).mapHomotopy (Ht k).some).compLeft _).trans (Homotopy.ofEq (e h).symm))

/-- Glueing a family of maps of complexes on the pieces is functorial. -/
theorem piMap_pushforward_comp
    {P C D : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    (g : ∀ k, P k ⟶ C k) (h : ∀ k, C k ⟶ D k) :
    (Limits.Pi.map fun k => (ψC[U k]).map (g k ≫ h k)) =
      (Limits.Pi.map fun k => (ψC[U k]).map (g k)) ≫
        Limits.Pi.map fun k => (ψC[U k]).map (h k) :=
  Pi.hom_ext _ _ fun k => by simp [Functor.map_comp]

/-- **Glueing a morphism along a clopen decomposition, at the level of complexes.** Let
`f : A ⟶ B` be a map of complexes of `𝒪_Y`-modules, and suppose that on each piece `Uₖ` of a
decomposition of `Y` into open and closed subschemes the restriction of `f` is identified in the
derived category with a map of complexes `αₖ : Pₖ ⟶ P'ₖ`. Then `f` is identified in `D(𝒪_Y)`
with the product `∏ₖ jₖ_* αₖ` of the pushforwards. -/
theorem exists_iso_Q_pi_pushforward_comm_of_hom (hU : IsClopenDecomposition U)
    {A B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ}
    (f : A ⟶ B)
    {P P' : ∀ k, CochainComplex (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y.toRingedSpace (U k)))) ℤ}
    (α : ∀ k, P k ⟶ P' k)
    (θ : ∀ k, DerivedCategory.Q.obj ((ρC[U k]).obj A) ≅ DerivedCategory.Q.obj (P k))
    (θ' : ∀ k, DerivedCategory.Q.obj ((ρC[U k]).obj B) ≅ DerivedCategory.Q.obj (P' k))
    (hθ : ∀ k, DerivedCategory.Q.map ((ρC[U k]).map f) ≫ (θ' k).hom =
      (θ k).hom ≫ DerivedCategory.Q.map (α k)) :
    ∃ (E : DerivedCategory.Q.obj A ≅
        DerivedCategory.Q.obj (∏ᶜ fun k => (ψC[U k]).obj (P k)))
      (E' : DerivedCategory.Q.obj B ≅
        DerivedCategory.Q.obj (∏ᶜ fun k => (ψC[U k]).obj (P' k))),
      DerivedCategory.Q.map f ≫ E'.hom =
        E.hom ≫ DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (α k)) := by
  choose C g s hs hfac using fun k => DerivedCategory.left_fac (θ k).hom
  choose C' g' s' hs' hfac' using fun k => DerivedCategory.left_fac (θ' k).hom
  choose V c r hr hfacr using fun k => DerivedCategory.left_fac
    (inv (DerivedCategory.Q.map (s k)) ≫ DerivedCategory.Q.map (α k ≫ s' k))
  have := hs
  have := hs'
  have := hr
  have hg : ∀ k, DerivedCategory.Q.map (g k) = (θ k).hom ≫ DerivedCategory.Q.map (s k) :=
    fun k => eq_comp_of_eq_comp_inv (hfac k)
  have hg' : ∀ k, DerivedCategory.Q.map (g' k) = (θ' k).hom ≫ DerivedCategory.Q.map (s' k) :=
    fun k => eq_comp_of_eq_comp_inv (hfac' k)
  -- The two equalities on each piece that are glued.
  have E1 : ∀ k, DerivedCategory.Q.map (s k ≫ c k) =
      DerivedCategory.Q.map (α k ≫ s' k ≫ r k) := fun k => by
    rw [Functor.map_comp, eq_comp_of_eq_comp_inv (hfacr k)]
    simp [Functor.map_comp]
  have E2 : ∀ k, DerivedCategory.Q.map ((ρC[U k]).map f ≫ g' k ≫ r k) =
      DerivedCategory.Q.map (g k ≫ c k) := fun k => by
    have hc : DerivedCategory.Q.map (s k) ≫ DerivedCategory.Q.map (c k) =
        DerivedCategory.Q.map (α k) ≫ DerivedCategory.Q.map (s' k) ≫
          DerivedCategory.Q.map (r k) := by
      simpa only [Functor.map_comp] using E1 k
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hg' k, Category.assoc,
      reassoc_of% (hθ k), hg k, Category.assoc, ← hc]
  -- Glueing them.
  have G1 := Q_map_piMap_pushforward_eq U hU (fun k => s k ≫ c k)
    (fun k => α k ≫ s' k ≫ r k) E1
  have G2 := Q_map_piMap_pushforward_eq U hU (fun k => (ρC[U k]).map f ≫ g' k ≫ r k)
    (fun k => g k ≫ c k) E2
  rw [piMap_pushforward_comp U s c, piMap_pushforward_comp U α (fun k => s' k ≫ r k),
    piMap_pushforward_comp U s' r] at G1
  rw [piMap_pushforward_comp U (fun k => (ρC[U k]).map f) (fun k => g' k ≫ r k),
    piMap_pushforward_comp U g' r, piMap_pushforward_comp U g c] at G2
  simp only [Functor.map_comp] at G1 G2
  have iη := fun M => (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_piLift_unit U hU M)
  have ig := isIso_Q_map_piMap_pushforward U hU g fun k => by rw [hg k]; infer_instance
  have ig' := isIso_Q_map_piMap_pushforward U hU g' fun k => by rw [hg' k]; infer_instance
  have is := isIso_Q_map_piMap_pushforward U hU s hs
  have is' := isIso_Q_map_piMap_pushforward U hU s' hs'
  have mr : Mono (DerivedCategory.Q.map (Limits.Pi.map fun k => (ψC[U k]).map (r k))) :=
    @IsIso.mono_of_iso _ _ _ _ _ (isIso_Q_map_piMap_pushforward U hU r hr)
  have hnat₀ : f ≫ (Pi.lift fun k => (adj[U k]).unit.app B) =
      (Pi.lift fun k => (adj[U k]).unit.app A) ≫
        Limits.Pi.map fun k => (ψC[U k]).map ((ρC[U k]).map f) :=
    Pi.hom_ext _ _ fun k => by simp
  have hnat := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map hnat₀).trans (DerivedCategory.Q.map_comp _ _))
  exact exists_iso_comp_hom_eq_of_fractions _ _ _ _ _ _ _ _ _ _ _ (hηA := iη A) (hηB := iη B)
    (hG := ig) (hS := is) (hG' := ig') (hS' := is') (hR := mr) hnat G1 G2

end Stacks.Chow.ClopenGlueing

/-! ### A morphism of perfect objects on a Noetherian scheme with the resolution property -/

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- **A morphism of perfect objects is a map of bounded complexes of finite locally free
modules**, on a Noetherian scheme with the resolution property. Both objects are represented by
bounded complexes of finite locally free modules ([Stacks, Tag 0F8F]), and the morphism between
the representatives is a roof of such complexes whose backwards arrow is a quasi-isomorphism
([Stacks, Tag 0F8G]); the source of the roof represents the source of the morphism. -/
theorem exists_boundedFiniteLocallyFree_hom_iso_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] [HasResolutionProperty X] {E F : DerivedCategory X.Modules}
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) (φ : E ⟶ F) :
    ∃ (P P' : CochainComplex X.Modules ℤ) (α : P ⟶ P') (e : E ≅ DerivedCategory.Q.obj P)
      (e' : F ≅ DerivedCategory.Q.obj P'),
      boundedFiniteLocallyFreeComplex X P ∧ boundedFiniteLocallyFreeComplex X P' ∧
        φ ≫ e'.hom = e.hom ≫ DerivedCategory.Q.map α := by
  obtain ⟨PE, hPE, ⟨eE⟩⟩ := exists_boundedFiniteLocallyFree_iso_of_isNoetherian X E hE
  obtain ⟨PF, hPF, ⟨eF⟩⟩ := exists_boundedFiniteLocallyFree_iso_of_isNoetherian X F hF
  obtain ⟨G, p, hp, q, hG, hpq⟩ := exists_boundedFiniteLocallyFree_roof_of_isNoetherian X PE PF
    hPE hPF (eE.hom ≫ φ ≫ eF.inv)
  refine ⟨G, PF, q, eE.symm ≪≫ (asIso (DerivedCategory.Q.map p)).symm, eF.symm, hG, hPF, ?_⟩
  change φ ≫ eF.inv = (eE.inv ≫ inv (DerivedCategory.Q.map p)) ≫ DerivedCategory.Q.map q
  rw [Category.assoc, hpq, Iso.inv_hom_id_assoc]

end Stacks.Perfect.BoundedLocallyFreeComplexes

/-! ### The envelope and the representation of the morphism -/

namespace Stacks.Chow

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.HigherDirectImage
  RingedSpaceModuleAdjunction in
/-- **A morphism of perfect objects after an envelope, over a locally Noetherian scheme.** Let
`X` be a locally Noetherian scheme whose irreducible components are quasi-compact, and let
`φ : E ⟶ F` be a morphism of perfect objects of `D(𝒪_X)`. There is an envelope `f : Y ⟶ X`
and a map `α : P ⟶ P'` of locally bounded complexes of finite locally free `𝒪_Y`-modules
which is identified with `Lf^*φ` in `D(𝒪_Y)`. -/
theorem exists_envelope_mapPresentation_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : ∀ Z ∈ irreducibleComponents X, IsCompact Z)
    {E F : DerivedCategory X.Modules}
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) (φ : E ⟶ F) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P P' : CochainComplex Y.Modules ℤ)
      (α : P ⟶ P')
      (e : DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E)
      (e' : DerivedCategory.Q.obj P' ≅ (derivedPullback f.toLRSHom.toShHom).obj F),
      IsLocallyBoundedFiniteLocallyFree P ∧ IsLocallyBoundedFiniteLocallyFree P' ∧
        DerivedCategory.Q.map α ≫ e'.hom =
          e.hom ≫ (derivedPullback f.toLRSHom.toShHom).map φ := by
  obtain ⟨Y, f, hf, I, U, hU, hUn⟩ := exists_isEnvelope_isClopenDecomposition_isNoetherian hX
  -- A map of complexes `g : A ⟶ B` on `Y` representing `Lf^*φ`.
  obtain ⟨A, ⟨eA⟩⟩ : ∃ A : CochainComplex (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) ℤ,
      Nonempty (DerivedCategory.Q.obj A ≅ (derivedPullback f.toLRSHom.toShHom).obj E) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso _⟩⟩
  obtain ⟨B₀, ⟨eB₀⟩⟩ : ∃ B : CochainComplex (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) ℤ,
      Nonempty (DerivedCategory.Q.obj B ≅ (derivedPullback f.toLRSHom.toShHom).obj F) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso _⟩⟩
  obtain ⟨B, g, s₀, hs₀, hfac⟩ := DerivedCategory.left_fac
    (eA.hom ≫ (derivedPullback f.toLRSHom.toShHom).map φ ≫ eB₀.inv)
  obtain ⟨eB, hg⟩ := exists_iso_comp_hom_eq eA eB₀ _ (DerivedCategory.Q.map g)
    (DerivedCategory.Q.map s₀) (hs := hs₀) hfac
  -- On each piece, the restriction of `g` is a map of bounded complexes of finite locally free
  -- modules in the derived category.
  have key : ∀ k, ∃ (P P' : CochainComplex (U k : Scheme.{u}).Modules ℤ) (α : P ⟶ P')
      (θ : DerivedCategory.Q.obj (((moduleRestriction Y.toRingedSpace (U k)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A) ≅ DerivedCategory.Q.obj P)
      (θ' : DerivedCategory.Q.obj (((moduleRestriction Y.toRingedSpace (U k)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B) ≅ DerivedCategory.Q.obj P'),
      Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex _ P ∧
        Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex _ P' ∧
        DerivedCategory.Q.map (((moduleRestriction Y.toRingedSpace (U k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) ≫ θ'.hom = θ.hom ≫ DerivedCategory.Q.map α := by
    intro k
    obtain ⟨_, _⟩ := hUn k
    have hperf : ∀ (M : CochainComplex (SheafOfModules.{u}
        (structureSheafRing Y.toRingedSpace)) ℤ) (G : DerivedCategory X.Modules),
        Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G →
        (DerivedCategory.Q.obj M ≅ (derivedPullback f.toLRSHom.toShHom).obj G) →
        Cohomology.PerfectComplexes.IsPerfect (X := (U k : Scheme.{u}).toRingedSpace)
          (DerivedCategory.Q.obj (((moduleRestriction Y.toRingedSpace (U k)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) := fun M G hG eM =>
      Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
        ((derivedPullback (U k).ι.toLRSHom.toShHom).mapIso eM.symm ≪≫
          (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso
            Y.toRingedSpace (U k)).app (DerivedCategory.Q.obj M) ≪≫
          (moduleRestriction Y.toRingedSpace (U k)).mapDerivedCategoryFactors.app M)
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ G hG))
    obtain ⟨P, P', α, θ, θ', hP, hP', hθ⟩ :=
      Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_hom_iso_of_isNoetherian
        (U k : Scheme.{u}) (hperf A E hE eA) (hperf B F hF eB)
        (DerivedCategory.Q.map (((moduleRestriction Y.toRingedSpace (U k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g))
    exact ⟨P, P', α, θ, θ', hP, hP', hθ⟩
  choose P P' α θ θ' hP hP' hθ using key
  -- Glueing.
  obtain ⟨E₀, E₀', hc⟩ := ClopenGlueing.exists_iso_Q_pi_pushforward_comm_of_hom U hU g α θ θ' hθ
  have hflf : ∀ (Q : ∀ k, CochainComplex (U k : Scheme.{u}).Modules ℤ),
      (∀ k, Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex _ (Q k)) →
      ∀ k n, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := StrictlyPerfect.structureSheafOfRings (U k : Scheme.{u}).toRingedSpace)
          ((Q k).X n) := fun Q hQ k n =>
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      ((hQ k).2 n).exists_isFiniteLocallyFreeData
  have hbd : ∀ (Q : ∀ k, CochainComplex (U k : Scheme.{u}).Modules ℤ),
      (∀ k, Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex _ (Q k)) →
      ∀ k, ∃ lo hi : ℤ, ∀ n, (n < lo ∨ hi < n) → IsZero ((Q k).X n) := fun Q hQ k => by
    obtain ⟨⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩, -⟩ := hQ k
    refine ⟨lo, hi, fun n hn => ?_⟩
    rcases hn with hn | hn
    · exact (Q k).isZero_of_isStrictlyGE lo n hn
    · exact (Q k).isZero_of_isStrictlyLE hi n hn
  refine ⟨Y, f, hf, _, _, Limits.Pi.map fun k => ((modulePushforward (openSubspaceInclusion
    Y.toRingedSpace (U k))).mapHomologicalComplex (ComplexShape.up ℤ)).map (α k),
    E₀.symm ≪≫ eA, E₀'.symm ≪≫ eB,
    ClopenGlueing.isLocallyBoundedFiniteLocallyFree_pi_pushforward U hU P (hflf P hP) (hbd P hP),
    ClopenGlueing.isLocallyBoundedFiniteLocallyFree_pi_pushforward U hU P' (hflf P' hP')
      (hbd P' hP'), ?_⟩
  exact comp_symm_trans_hom_eq _ _ _ E₀ E₀' eA eB hc hg

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **A morphism of perfect objects after an envelope.** Let `X` be locally of finite type over
the base of chapter 42 of the Stacks Project with quasi-compact irreducible components, and let
`φ : E ⟶ F` be a morphism of perfect objects of `D(𝒪_X)`. There is an envelope `f : Y ⟶ X`
such that `Lf^*φ` is represented by a map `α : P ⟶ P'` of locally bounded complexes of finite
locally free `𝒪_Y`-modules: there are isomorphisms `Q(P) ≅ Lf^*E` and `Q(P') ≅ Lf^*F` under
which `Q(α)` is `Lf^*φ`. This is the step "(3) implies (1)" of the proof of Stacks 0F9F. -/
theorem exists_envelope_mapPresentation_of_isCompact_irreducibleComponents
    (C : ChowSituation.{u}) {X : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a]
    (hX : ∀ Z ∈ irreducibleComponents X, IsCompact Z)
    {E F : DerivedCategory X.Modules}
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) (φ : E ⟶ F) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P P' : CochainComplex Y.Modules ℤ)
      (α : P ⟶ P')
      (e : DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E)
      (e' : DerivedCategory.Q.obj P' ≅ (derivedPullback f.toLRSHom.toShHom).obj F),
      IsLocallyBoundedFiniteLocallyFree P ∧ IsLocallyBoundedFiniteLocallyFree P' ∧
        DerivedCategory.Q.map α ≫ e'.hom =
          e.hom ≫ (derivedPullback f.toLRSHom.toShHom).map φ :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  exists_envelope_mapPresentation_of_isLocallyNoetherian hX hE hF φ

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **A morphism of perfect objects after an envelope, `X` quasi-compact.** Let `X` be
quasi-compact and locally of finite type over the base of chapter 42 of the Stacks Project, and
let `φ : E ⟶ F` be a morphism of perfect objects of `D(𝒪_X)`. There is an envelope
`f : Y ⟶ X` such that `Lf^*φ` is represented by a map of locally bounded complexes of finite
locally free `𝒪_Y`-modules: the irreducible components of `X` are closed, hence quasi-compact,
and `Stacks.Chow.exists_envelope_mapPresentation_of_isCompact_irreducibleComponents`
applies. -/
theorem exists_envelope_mapPresentation_of_compactSpace (C : ChowSituation.{u})
    {X : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a] [CompactSpace X]
    {E F : DerivedCategory X.Modules}
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hF : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F) (φ : E ⟶ F) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P P' : CochainComplex Y.Modules ℤ)
      (α : P ⟶ P')
      (e : DerivedCategory.Q.obj P ≅ (derivedPullback f.toLRSHom.toShHom).obj E)
      (e' : DerivedCategory.Q.obj P' ≅ (derivedPullback f.toLRSHom.toShHom).obj F),
      IsLocallyBoundedFiniteLocallyFree P ∧ IsLocallyBoundedFiniteLocallyFree P' ∧
        DerivedCategory.Q.map α ≫ e'.hom =
          e.hom ≫ (derivedPullback f.toLRSHom.toShHom).map φ :=
  exists_envelope_mapPresentation_of_isCompact_irreducibleComponents C a
    (fun Z hZ => (isClosed_of_mem_irreducibleComponents Z hZ).isCompact) hE hF φ

end Stacks.Chow

end
