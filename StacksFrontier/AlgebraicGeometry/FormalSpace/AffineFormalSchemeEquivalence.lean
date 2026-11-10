module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClassicalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Affine formal schemes are the classical affine formal algebraic spaces (Stacks 0AIE)

Let `B` be a big fppf site and `S` a terminal scheme of it, the source's `Spec(ℤ)`. Stacks 0AIE
shows that `𝔛 ↦ h_𝔛` identifies affine formal schemes à la EGA with classical affine formal
algebraic spaces over `S`, as long as the big site is chosen compatibly. "Compatibly" means that
for `𝔛 = Spf A` the coproduct of the schemes `Spec (A/I)`, over the ideals of definition `I` of
`A`, belongs to the site. This file proves that equivalence of categories, and the statements of
the remark about the type of `h_𝔛`, under exactly that size hypothesis.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsSmallAffineFormalScheme`: the affine formal schemes `Spf A`
  whose coproduct `∐_I Spec (A/I)` lies in the site.
* `AlgebraicGeometry.FormalSpace.smallAffineFormalSchemePointsFunctor`: `𝔛 ↦ h_𝔛`, from those
  affine formal schemes to classical affine formal algebraic spaces over `S`.
* `AlgebraicGeometry.FormalSpace.smallAffineFormalSchemeEquivalence`: the resulting equivalence.

## Main results

* `AlgebraicGeometry.FormalSpace.contains_sigmaSpec_iff`: for `A` admissible, the coproduct
  `∐_I Spec (A/I)` lies in the site exactly when `#A` is below the cutoff.
* `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_weakIdealColimitPresentation`: a ring presenting
  an fppf sheaf that satisfies the set-theoretic condition of Stacks 0AIS is smaller than the
  cutoff.
* `AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf_of_contains` and its
  affineness half: **Stacks 0AIE**, `h_{Spf A}` is a classical affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isEquivalence_smallAffineFormalSchemePointsFunctor`:
  **Stacks 0AIE**, the equivalence of categories.

## Implementation notes

Both size conditions involved come down to the cardinality of `A`. The coproduct of the
quotient spectra lies in the site exactly when `#A` is below the cutoff. One direction is a
count. For the other, `A` injects into the maps from the coproduct to the affine line, which are
the global functions on the coproduct, because `A` is separated and its ideals of definition
form a basis of neighbourhoods of zero. On the other side a classical affine formal algebraic
space `X` comes with a surjection `h_U ⟶ X` from a scheme `U` of the site. Its presenting ring
injects into `Mor(X, 𝒪)`, which injects into `Mor(h_U, 𝒪) = Γ(U, 𝒪_U)`. So an object of either
category has a ring below the cutoff. Its quotient spectra then form a quotient system over the
terminal base, to which the colimit formula
`AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison` applies. The functor is fully
faithful by Stacks 0AI1, in the form
`AlgebraicGeometry.FormalSpace.exists_map_eq_formalSchemePointsFppfSheafFunctor`.

## References

* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Separation -/

section Separation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- In a separated linearly topologized ring every nonzero element lies outside some open
ideal. -/
theorem exists_isOpen_ideal_not_mem [T2Space A] {a : A} (ha : a ≠ 0) :
    ∃ J : Ideal A, IsOpen (J : Set A) ∧ a ∉ J := by
  obtain ⟨J, hJ, hJa⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Ne.symm ha))
  exact ⟨J, hJ, fun h => hJa h rfl⟩

/-- In a separated linearly topologized ring, a nonzero element lies outside some open ideal
contained in any given open ideal. -/
private theorem exists_le_isOpen_ideal_not_mem [T2Space A] {a : A} (ha : a ≠ 0) {I : Ideal A}
    (hI : IsOpen (I : Set A)) : ∃ K ≤ I, IsOpen (K : Set A) ∧ a ∉ K := by
  obtain ⟨J, hJ, haJ⟩ := exists_isOpen_ideal_not_mem ha
  exact ⟨I ⊓ J, inf_le_left, by simpa using hI.inter hJ, fun h => haJ (Ideal.mem_inf.1 h).2⟩

/-- Two elements of an admissible topological ring with the same image in `A/I` for every ideal
of definition `I` are equal. -/
theorem eq_of_forall_idealsOfDefinition (hA : TopologicalRing.IsAdmissible A) {a b : A}
    (h : ∀ I : IdealsOfDefinition A, Ideal.Quotient.mk I.1 a = Ideal.Quotient.mk I.1 b) :
    a = b := by
  have : T2Space A := hA.2.1
  by_contra hne
  obtain ⟨I₀, hI₀⟩ := hA.1
  obtain ⟨K, hKI, hK, hab⟩ := exists_le_isOpen_ideal_not_mem (sub_ne_zero.2 hne) hI₀.1
  exact hab (Ideal.Quotient.eq.mp
    (h ⟨K, TopologicalRing.isIdealOfDefinition_of_le_of_isOpen hI₀ hK hKI⟩))

/-- Two elements of a weakly admissible topological ring with the same image in `A/J` for every
weak ideal of definition `J` are equal. -/
theorem eq_of_forall_weakIdeals (hA : TopologicalRing.IsWeaklyAdmissible A) {a b : A}
    (h : ∀ J : WeakIdeals A, Ideal.Quotient.mk J.1 a = Ideal.Quotient.mk J.1 b) : a = b := by
  have : T2Space A := hA.2.2
  by_contra hne
  obtain ⟨I₀, hI₀⟩ := hA.1
  obtain ⟨K, hKI, hK, hab⟩ := exists_le_isOpen_ideal_not_mem (sub_ne_zero.2 hne) hI₀.1
  exact hab (Ideal.Quotient.eq.mp
    (h (OrderDual.toDual ⟨K, hK, fun x hx => hI₀.2 x (hKI hx)⟩)))

end Separation

/-! ### The size of the coproduct of the quotient spectra -/

section CoproductSize

variable (B : BigFppfSite.{u})

/-- The global functions on a scheme contained in a big fppf site are fewer than the cutoff. -/
theorem mk_sections_top_lt_cutoff {X : Scheme.{u}} (hX : B.Contains X) :
    #Γ(X, ⊤) < B.cutoff :=
  (X.mk_sections_le_two_pow_size ⊤).trans_lt (B.cutoff_isStrongPrelimit hX)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- If the coproduct of the spectra `Spec (A/I)` of an admissible topological ring, over its
ideals of definition, belongs to a big fppf site, then `A` is smaller than the cutoff: `A`
injects into the morphisms from the coproduct to the affine line, which are its global
functions. -/
theorem mk_lt_cutoff_of_contains_sigmaSpec (hA : TopologicalRing.IsAdmissible A)
    (hB : B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I))) :
    #A < B.cutoff := by
  set X := ∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I)
  let e := Stacks.Sites.globalSectionsIsoYoneda.{u}
  let pt : ∀ I : IdealsOfDefinition A, A →
      (Spec (spfQuotient A I) ⟶ Stacks.Sites.affineLineOverInt.{u}) := fun I a =>
    (e.app (op (Spec (spfQuotient A I)))).hom
      ((Scheme.ΓSpecIso (spfQuotient A I)).inv (Ideal.Quotient.mk I.1 a))
  have hinj : Function.Injective fun a : A =>
      (Sigma.desc fun I => pt I a : X ⟶ Stacks.Sites.affineLineOverInt.{u}) := by
    intro a b hab
    refine eq_of_forall_idealsOfDefinition hA fun I => ?_
    have h1 : pt I a = pt I b := by
      simpa using congrArg
        (fun g => Sigma.ι (fun I : IdealsOfDefinition A => Spec (spfQuotient A I)) I ≫ g) hab
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (spfQuotient A I)).inv).1
      ((e.app (op (Spec (spfQuotient A I)))).toEquiv.injective h1)
  calc #A ≤ #(X ⟶ Stacks.Sites.affineLineOverInt.{u}) := mk_le_of_injective hinj
    _ = #Γ(X, ⊤) := Cardinal.mk_congr (e.app (op X)).toEquiv.symm
    _ < B.cutoff := mk_sections_top_lt_cutoff B hB

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A ring smaller than the cutoff of a big fppf site has the coproduct of its quotient spectra
by ideals of definition in the site: there are at most `2 ^ #A` ideals, and each quotient is no
larger than `A`. -/
theorem contains_sigmaSpec_of_mk_lt_cutoff (hA : #A < B.cutoff) :
    B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I)) := by
  classical
  set κ : Cardinal.{u} := max ℵ₀ (2 ^ #A)
  have hκ : κ < B.cutoff := max_lt B.aleph0_lt_cutoff (B.cutoff_isStrongPrelimit hA)
  have hι : #(IdealsOfDefinition A) ≤ κ := by
    calc #(IdealsOfDefinition A) ≤ #(Ideal A) := mk_subtype_le _
      _ ≤ #(Set A) := mk_le_of_injective (f := fun J : Ideal A => (J : Set A))
          SetLike.coe_injective
      _ = 2 ^ #A := mk_set
      _ ≤ κ := le_max_right _ _
  refine lt_of_le_of_lt (schemeSize_coproduct_le _ κ (le_max_left _ _) hι fun I => ?_) hκ
  rw [Scheme.size_Spec]
  exact max_le (le_max_left _ _)
    ((mk_le_of_surjective Ideal.Quotient.mk_surjective).trans
      ((Cardinal.cantor _).le.trans (le_max_right _ _)))

/-- For an admissible topological ring `A`, the coproduct of the spectra `Spec (A/I)` over the
ideals of definition belongs to a big fppf site exactly when `A` is smaller than its cutoff. -/
theorem contains_sigmaSpec_iff (hA : TopologicalRing.IsAdmissible A) :
    B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I)) ↔ #A < B.cutoff :=
  ⟨mk_lt_cutoff_of_contains_sigmaSpec B hA, contains_sigmaSpec_of_mk_lt_cutoff B⟩

end CoproductSize

/-! ### The presenting ring of a sheaf satisfying the set-theoretic condition -/

section PresentingRing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global functions form a sheaf of sets on the big fppf site of `S`, with values in the
universe of `AlgebraicGeometry.FormalSpace.FppfSheaf`. -/
theorem isSheaf_globalFunctions :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat ⋙
        uliftFunctor.{u + 1}) := by
  have h₀ : Presheaf.IsSheaf B.topology (B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (BigFppfSite.isSheaf_globalSections B)
  have h₁ := (Sheaf.over (⟨_, h₀⟩ : Sheaf B.topology (Type u)) (B.obj hS)).property
  rw [isSheaf_iff_isSheaf_of_type] at h₁ ⊢
  exact Presieve.isSheaf_comp_uliftFunctor (h := h₁)

/-- The sheaf of global functions on the big fppf site of `S`. -/
def globalFunctionsFppfSheaf : FppfSheaf B S hS :=
  ⟨_, isSheaf_globalFunctions B S hS⟩

variable {B S hS} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] {X : FppfSheaf B S hS}

local notation "τ" => BigFppfOver.topology B S hS

/-- The global function on the stage `J` of a presentation by `A` given by `a ∈ A`. -/
def presentationStageFunction (P : WeakIdealColimitPresentation B S hS A X) (J : WeakIdeals A)
    (a : A) :
    (globalFunctionsFppfSheaf B S hS).obj.obj
      (op ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J))) :=
  ULift.up (Scheme.Γ.map (P.quotientIso J).hom.op
    ((Scheme.ΓSpecIso (.of (A ⧸ J.1))).inv (Ideal.Quotient.mk J.1 a)))

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The global functions of a presentation given by `a ∈ A` are compatible with the transition
morphisms. -/
theorem globalFunctions_map_presentationStageFunction
    (P : WeakIdealColimitPresentation B S hS A X) {J K : WeakIdeals A} (f : J ⟶ K) (a : A) :
    (globalFunctionsFppfSheaf B S hS).obj.map
        ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)).op
        (presentationStageFunction P K a) =
      presentationStageFunction P J a := by
  set g := (BigAffineFppf.toScheme B S hS).map (P.diagram.map f)
  set φ := CommRingCat.ofHom (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f))
  have e₁ : Scheme.Γ.map (g ≫ (P.quotientIso K).hom).op =
      Scheme.Γ.map ((P.quotientIso J).hom ≫ Spec.map φ).op := by
    rw [P.quotientIso_natural f]
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at e₁
  have e₂ := ConcreteCategory.congr_hom e₁
    ((Scheme.ΓSpecIso (.of (A ⧸ K.1))).inv (Ideal.Quotient.mk K.1 a))
  have e₃ := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ)
    (Ideal.Quotient.mk K.1 a)
  exact congrArg ULift.up (e₂.trans
    (congrArg (ConcreteCategory.hom (Scheme.Γ.map (P.quotientIso J).hom.op)) e₃.symm))

/-- The cocone, with vertex the sheaf of global functions, given by `a ∈ A` on the diagram of a
presentation by `A`. -/
def presentationCocone (P : WeakIdealColimitPresentation B S hS A X) (a : A) :
    Cocone (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) where
  pt := globalFunctionsFppfSheaf B S hS
  ι :=
    { app J := (Sheaf.sectionEquiv τ).symm (presentationStageFunction P J a)
      naturality J K f := by
        change (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f)) ≫
            (Sheaf.sectionEquiv τ).symm (presentationStageFunction P K a) =
          (Sheaf.sectionEquiv τ).symm (presentationStageFunction P J a) ≫ 𝟙 _
        rw [Category.comp_id, ← Sheaf.sectionEquiv_symm_map,
          globalFunctions_map_presentationStageFunction] }

/-- The global function on a sheaf presented by `A` given by `a ∈ A`. -/
def presentationFunction (P : WeakIdealColimitPresentation B S hS A X) (a : A) :
    X ⟶ globalFunctionsFppfSheaf B S hS :=
  P.colimitIso.hom ≫ colimit.desc _ (presentationCocone P a)

/-- Over a weakly admissible ring, distinct elements give distinct global functions on a sheaf
presented by the ring. -/
theorem injective_presentationFunction (hA : TopologicalRing.IsWeaklyAdmissible A)
    (P : WeakIdealColimitPresentation B S hS A X) :
    Function.Injective (presentationFunction P) := by
  intro a b hab
  refine eq_of_forall_weakIdeals hA fun J => ?_
  have hι : ∀ c : A, (Sheaf.sectionEquiv τ).symm (presentationStageFunction P J c) =
      colimit.ι _ J ≫ P.colimitIso.inv ≫ presentationFunction P c := fun c => by
    change _ = colimit.ι _ J ≫ P.colimitIso.inv ≫ P.colimitIso.hom ≫
      colimit.desc _ (presentationCocone P c)
    rw [Iso.inv_hom_id_assoc]
    exact (colimit.ι_desc (presentationCocone P c) J).symm
  have h3 : (Sheaf.sectionEquiv τ).symm (presentationStageFunction P J a) =
      (Sheaf.sectionEquiv τ).symm (presentationStageFunction P J b) := by
    rw [hι, hι, hab]
  have h4 := congrArg ULift.down ((Sheaf.sectionEquiv τ).symm.injective h3)
  have h5 := (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map (P.quotientIso J).hom.op)).1 h4
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ J.1))).inv).1 h5

/-- A weakly admissible topological ring presenting an fppf sheaf which satisfies the
set-theoretic condition of Stacks 0AIS is smaller than the cutoff of the site.

The condition supplies an epimorphism `h_U ⟶ X` from a representable sheaf. The ring injects
into the global functions on `X` (`AlgebraicGeometry.FormalSpace.injective_presentationFunction`),
these inject into the global functions on `h_U` because `h_U ⟶ X` is an epimorphism, and those
are `Γ(U, 𝒪_U)`, smaller than the cutoff since `U` is in the site. -/
theorem mk_lt_cutoff_of_weakIdealColimitPresentation
    (hA : TopologicalRing.IsWeaklyAdmissible A) (P : WeakIdealColimitPresentation B S hS A X)
    (hX : SatisfiesSetTheoreticCondition B S hS X) : #A < B.cutoff := by
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, f, hf, -⟩ := hX
  let Ψ : (X ⟶ globalFunctionsFppfSheaf B S hS) →
      (globalFunctionsFppfSheaf B S hS).obj.obj (op U) := fun ψ =>
    (f ≫ ψ).hom.app (op U) (eU.inv.app (op U) (ULift.up (𝟙 U)))
  have hΨ : Function.Injective Ψ := by
    intro ψ₁ ψ₂ h
    exact (cancel_epi f).1 (Sheaf.hom_ext ((cancel_epi eU.inv).1 (uliftYonedaEquiv.injective h)))
  have hcard : Cardinal.lift.{u + 1} #A ≤
      Cardinal.lift.{u + 1} #Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := by
    rw [← mk_uLift, ← mk_uLift]
    exact (mk_le_of_injective ((injective_presentationFunction hA P).comp
      ULift.down_injective)).trans (mk_le_of_injective hΨ)
  exact (lift_le.1 hcard).trans_lt
    (mk_sections_top_lt_cutoff B (X := (BigFppfOver.toScheme B S hS).obj U) U.left.property)

end PresentingRing

/-! ### The equivalence -/

section Equivalence

variable (B : BigFppfSite.{u})

/-- **The affine formal schemes of Stacks 0AIE, for a compatible big fppf site.** A formal scheme
isomorphic to the formal spectrum `Spf A` of an admissible topological ring `A` such that the
coproduct of the schemes `Spec (A/I)`, over the ideals of definition `I` of `A`, belongs to the
site `B`. -/
abbrev IsSmallAffineFormalScheme : ObjectProperty FormalScheme.{u} := fun X =>
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (hA : TopologicalRing.IsAdmissible A),
    Nonempty (X ≅ spfFormalScheme A hA) ∧
      B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I))

section Ring

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- A formal scheme isomorphic to `Spf A`, for `A` admissible and smaller than an uncountable
cardinal `κ`, satisfies the size condition of Stacks 0AI1 for `κ`. -/
theorem isSizeBoundedFormalScheme_of_iso_spfFormalScheme {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hA : TopologicalRing.IsAdmissible A) (hAκ : #A < κ) {X : FormalScheme.{u}}
    (e : X ≅ spfFormalScheme A hA) : IsSizeBoundedFormalScheme κ X.obj := by
  have hsize : ∀ I : IdealsOfDefinition A, (Spec (spfQuotient A I)).size < κ := fun I => by
    rw [Scheme.size_Spec]
    exact max_lt hκ ((mk_le_of_surjective Ideal.Quotient.mk_surjective).trans_lt hAκ)
  let eP : X.obj.toPresheafedSpace ≅ (spfLTRS A hA.1).toPresheafedSpace :=
    { hom := e.hom.hom.toHom
      inv := e.inv.hom.toHom
      hom_inv_id := congrArg (fun g => g.hom.toHom) e.hom_inv_id
      inv_hom_id := congrArg (fun g => g.hom.toHom) e.inv_hom_id }
  exact fun _ => ⟨⊤, trivial, TopCommRingCat.of A, inferInstance, hA, hsize,
    ⟨PresheafedSpace.restrictTopIso _ ≪≫ eP⟩⟩

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- Over a terminal base, the quotient system of a ring smaller than the cutoff: every quotient
spectrum lies in the site, and the structure morphisms are the unique ones. -/
def quotientSystemOfIsTerminal (hterm : IsTerminal S) (hAc : #A < B.cutoff) :
    QuotientSystem B S hS A where
  inSite J := by
    change (Spec (.of (A ⧸ J.1))).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff
      ((mk_le_of_surjective Ideal.Quotient.mk_surjective).trans_lt hAc)
  overS _ := hterm.from _
  compatible _ _ _ := hterm.hom_ext _ _

/-- **Stacks 0AIE.** Over a terminal base, the functor of points of an affine formal scheme
`Spf A` is a classical affine formal algebraic space as soon as the coproduct of the schemes
`Spec (A/I)`, over the ideals of definition of `A`, belongs to the big fppf site. -/
@[stacks 0AIE "if the coproduct of the Spec(A/I) over the ideals of definition belongs to the \
site, then h_X is a classical affine formal algebraic space"]
theorem isClassical_formalSchemePointsFppfSheaf_of_contains (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) {X : FormalScheme.{u}} (e : X ≅ spfFormalScheme A hA)
    (hB : B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I))) :
    IsClassical B S hS (formalSchemePointsFppfSheaf B S hS X) := by
  have hAc := mk_lt_cutoff_of_contains_sigmaSpec B hA hB
  let D := quotientSystemOfIsTerminal B S hS hterm hAc
  exact isClassical_of_iso B S hS ((formalSchemePointsFppfSheafFunctor B S hS).mapIso e).symm
    (isClassical_formalSchemePointsFppfSheaf hterm hA D (hasLargeSite_of_mk_lt_cutoff D hAc))

/-- **Stacks 0AIE.** Over a terminal base, the functor of points of an affine formal scheme
`Spf A` is an affine formal algebraic space as soon as the coproduct of the schemes
`Spec (A/I)`, over the ideals of definition of `A`, belongs to the big fppf site. -/
@[stacks 0AIE "if the coproduct of the Spec(A/I) over the ideals of definition belongs to the \
site, then h_X is an affine formal algebraic space"]
theorem isAffineFormalAlgebraicSpace_formalSchemePointsFppfSheaf_of_contains
    (hterm : IsTerminal S) (hA : TopologicalRing.IsAdmissible A) {X : FormalScheme.{u}}
    (e : X ≅ spfFormalScheme A hA)
    (hB : B.Contains (∐ fun I : IdealsOfDefinition A => Spec (spfQuotient A I))) :
    IsAffineFormalAlgebraicSpace B S hS (formalSchemePointsFppfSheaf B S hS X) :=
  (isClassical_formalSchemePointsFppfSheaf_of_contains B S hS hterm hA e hB).1.1

end Ring

/-- An affine formal scheme in the size range of `B` satisfies the size condition of Stacks 0AI1
for the cutoff of `B`. -/
theorem isSizeBoundedFormalScheme_of_isSmallAffineFormalScheme {X : FormalScheme.{u}}
    (hX : IsSmallAffineFormalScheme B X) : IsSizeBoundedFormalScheme B.cutoff X.obj := by
  obtain ⟨A, _, _, _, _, hA, ⟨e⟩, hB⟩ := hX
  exact isSizeBoundedFormalScheme_of_iso_spfFormalScheme B.aleph0_lt_cutoff hA
    (mk_lt_cutoff_of_contains_sigmaSpec B hA hB) e

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor of points `𝔛 ↦ h_𝔛`, from the affine formal schemes in the size range of `B` to
the classical affine formal algebraic spaces over a terminal base `S`. -/
def smallAffineFormalSchemePointsFunctor (hterm : IsTerminal S) :
    (IsSmallAffineFormalScheme B).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (IsClassical B S hS) :=
  ObjectProperty.lift _
    ((IsSmallAffineFormalScheme B).ι ⋙ formalSchemePointsFppfSheafFunctor B S hS) fun X => by
      obtain ⟨A, _, _, _, _, hA, ⟨e⟩, hB⟩ := X.property
      exact isClassical_formalSchemePointsFppfSheaf_of_contains B S hS hterm hA e hB

/-- The functor of points on the affine formal schemes in the size range of `B` is the functor
of points of formal schemes. -/
theorem smallAffineFormalSchemePointsFunctor_comp_ι (hterm : IsTerminal S) :
    smallAffineFormalSchemePointsFunctor B S hS hterm ⋙ ObjectProperty.ι (IsClassical B S hS) =
      (IsSmallAffineFormalScheme B).ι ⋙ formalSchemePointsFppfSheafFunctor B S hS :=
  rfl

/-- The functor of points on the affine formal schemes in the size range of `B` is fully
faithful, by Stacks 0AI1. -/
def fullyFaithfulSmallAffineFormalSchemePointsFunctor (hterm : IsTerminal S) :
    (smallAffineFormalSchemePointsFunctor B S hS hterm).FullyFaithful where
  preimage {X _} φ := ObjectProperty.homMk
    (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm
      (isSizeBoundedFormalScheme_of_isSmallAffineFormalScheme B X.property) φ.hom).choose
  map_preimage {X _} φ := by
    apply ObjectProperty.hom_ext
    exact (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm
      (isSizeBoundedFormalScheme_of_isSmallAffineFormalScheme B X.property) φ.hom).choose_spec
  preimage_map {X _} f := by
    apply ObjectProperty.hom_ext
    refine injective_map_formalSchemePointsFppfSheafFunctor B S hS hterm
      (isSizeBoundedFormalScheme_of_isSmallAffineFormalScheme B X.property) ?_
    exact (exists_map_eq_formalSchemePointsFppfSheafFunctor B S hS hterm
      (isSizeBoundedFormalScheme_of_isSmallAffineFormalScheme B X.property)
      ((smallAffineFormalSchemePointsFunctor B S hS hterm).map f).hom).choose_spec

/-- Every classical affine formal algebraic space over a terminal base is the functor of points
of an affine formal scheme in the size range of `B`. Its admissible presenting ring `A` is
smaller than the cutoff, by the set-theoretic condition, so `Spf A` is in the size range, and
the colimit formula identifies the space with `h_{Spf A}`. -/
theorem essSurj_smallAffineFormalSchemePointsFunctor (hterm : IsTerminal S) :
    (smallAffineFormalSchemePointsFunctor B S hS hterm).EssSurj where
  mem_essImage Y := by
    obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hA⟩ := Y.property
    have hAc : #A < B.cutoff := hpr.2.elim fun P =>
      mk_lt_cutoff_of_weakIdealColimitPresentation hpr.1 P hpres.1.1
    obtain ⟨D, ⟨eD⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hpr
    exact ⟨⟨spfFormalScheme A hA, A, instCR, instTS, instTR, instLT, hA, ⟨Iso.refl _⟩,
      contains_sigmaSpec_of_mk_lt_cutoff B hAc⟩,
      ⟨(ObjectProperty.ι _).preimageIso
        ((spfFormalSchemeFppfComparisonIso hterm hA D).symm ≪≫ eD.symm)⟩⟩

/-- **Stacks 0AIE**, the equivalence. Over a terminal base `S` (the source's `Spec(ℤ)`), the
functor of points `𝔛 ↦ h_𝔛` is an equivalence from the category of affine formal schemes
`Spf A` whose coproduct `∐_I Spec (A/I)` belongs to the big fppf site `B` (the source's
"compatible choices of big site") to the category of classical affine formal algebraic spaces
over `S`. -/
@[stacks 0AIE "the category of affine formal schemes is equivalent to the category of classical \
affine formal algebraic spaces, by the functor of points"]
theorem isEquivalence_smallAffineFormalSchemePointsFunctor (hterm : IsTerminal S) :
    (smallAffineFormalSchemePointsFunctor B S hS hterm).IsEquivalence :=
  have := (fullyFaithfulSmallAffineFormalSchemePointsFunctor B S hS hterm).full
  have := (fullyFaithfulSmallAffineFormalSchemePointsFunctor B S hS hterm).faithful
  have := essSurj_smallAffineFormalSchemePointsFunctor B S hS hterm
  { }

/-- The equivalence of Stacks 0AIE between the affine formal schemes in the size range of `B`
and the classical affine formal algebraic spaces over a terminal base, given by the functor of
points. -/
def smallAffineFormalSchemeEquivalence (hterm : IsTerminal S) :
    (IsSmallAffineFormalScheme B).FullSubcategory ≌
      ObjectProperty.FullSubcategory (IsClassical B S hS) :=
  have := isEquivalence_smallAffineFormalSchemePointsFunctor B S hS hterm
  (smallAffineFormalSchemePointsFunctor B S hS hterm).asEquivalence

end Equivalence

end AlgebraicGeometry.FormalSpace

end
