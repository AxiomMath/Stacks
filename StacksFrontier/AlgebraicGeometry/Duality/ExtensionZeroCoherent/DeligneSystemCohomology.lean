module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionIso
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemSourcePresentation
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTrianglesCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerSystemProIso
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.TruncationDevissage
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Systems pro-isomorphic to Deligne systems, characterized by their cohomology

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and `𝓘 ⊆ 𝒪_X` a quasi-coherent
sheaf of ideals cutting out `X ∖ U`. [Stacks, Tag 0G4S] characterizes the inverse systems `(K_n)`
of `D^b_{Coh}(𝒪_X)` with cohomology in a fixed range `[a, b]` that are pro-isomorphic to a
Deligne system: exactly those for which every cohomology system `(H^p(K_n))` is pro-isomorphic to
the system `(𝓘^n𝓕)` of ideal powers of a coherent `𝒪_X`-module `𝓕`.

## Main results

* `AlgebraicGeometry.DeligneSystem.nonempty_proIso_homology`: the cohomology systems of a Deligne
  system, for an arbitrary ideal sheaf cutting out `X ∖ U`; this is (1) ⇒ (2).
* `AlgebraicGeometry.DeligneSystem.exists_proIso_of_single`: a system concentrated in one degree
  `p` whose cohomology there is pro-isomorphic to `(𝓘^n𝓕)` is pro-isomorphic to the Deligne
  system of `𝓕` placed in degree `p`; this is the base case of (2) ⇒ (1).
* `AlgebraicGeometry.DeligneSystem.proIsoDeligneSystem_of_homology`: (2) ⇒ (1).
* `AlgebraicGeometry.DeligneSystem.proIsoDeligneSystem_iff_homology`: **[Stacks, Tag 0G4S]**.

## References

* [Stacks Project, Tag 0G4S](https://stacks.math.columbia.edu/tag/0G4S)
* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
* [Stacks Project, Tag 0G4Q](https://stacks.math.columbia.edu/tag/0G4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open InverseSequence

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DeligneSystem

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- **The cohomology systems of a Deligne system.** For a Deligne system `(K_n)` and any
quasi-coherent sheaf of ideals `𝓘` cutting out `X ∖ U`, the system `(H^p(K_n))` is
pro-isomorphic to `(𝓘^n H^p(𝓕^•))`, where `𝓕^•` is the complex of the Deligne system.

The system `(H^p(K_n))` is `(H^p(𝓘_D^n𝓕^•))` for the ideal `𝓘_D` of the Deligne system
(`AlgebraicGeometry.DeligneSystem.homologySystemIso`), which is pro-isomorphic to
`(𝓘_D^n H^p(𝓕^•))` by [Stacks, Tag 0G4R]; and `𝓘_D` may be replaced by `𝓘`, the two having the
same vanishing locus (`Stacks.Duality.nonempty_proIso_idealPowerSystem`). -/
public theorem nonempty_proIso_homology (D : DeligneSystem j) (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range j.base)ᶜ) (p : ℤ) :
    Nonempty (ProIso ((D.system ⋙ (boundedCoherentDerived X).ι) ⋙
        DerivedCategory.homologyFunctor X.Modules p)
      (Stacks.Duality.idealPowerSystem I (D.complex.homology p))) := by
  obtain ⟨e₁⟩ := Stacks.Duality.cohomologyIdealPowersProIso D.idealSheaf D.complex p
    D.isCoherent_complex D.powers
  obtain ⟨e₂⟩ := Stacks.Duality.nonempty_proIso_idealPowerSystem
    (TopologicalSpace.Closeds.ext (D.support_idealSheaf.trans hI.symm))
    (Iso.refl (D.complex.homology p))
  exact ⟨Pro.proIsoTrans (Pro.proIsoOfNatIso (D.homologySystemIso p)) (Pro.proIsoTrans e₁ e₂)⟩

/-- **[Stacks, Tag 0G4S], (1) ⇒ (2).** If an inverse system `(K_n)` of `D^b_{Coh}(𝒪_X)` is
pro-isomorphic to a Deligne system, then for every quasi-coherent sheaf of ideals `𝓘` cutting
out `X ∖ U` and every `p`, the system `(H^p(K_n))` is pro-isomorphic to `(𝓘^n𝓕)` for a coherent
`𝒪_X`-module `𝓕`, namely `H^p` of the complex of the Deligne system. -/
public theorem exists_proIso_homology_of_proIso (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range j.base)ᶜ) (K : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hK : ProIsoDeligneSystem j K) (p : ℤ) :
    ∃ F : X.Modules, F.IsCoherent ∧
      Nonempty (ProSeq.of ((K ⋙ (boundedCoherentDerived X).ι) ⋙
        DerivedCategory.homologyFunctor X.Modules p) ≅
          ProSeq.of (Stacks.Duality.idealPowerSystem I F)) := by
  obtain ⟨D, ⟨i⟩⟩ := hK
  obtain ⟨e⟩ := D.nonempty_proIso_homology I hI p
  exact ⟨D.complex.homology p, D.isCoherent_homology p,
    ⟨ProSeq.isoOfProIso (Pro.proIsoTrans (Pro.proIsoWhiskerRight (ProSeq.proIsoOfIso i)
      ((boundedCoherentDerived X).ι ⋙ DerivedCategory.homologyFunctor X.Modules p)) e)⟩⟩

omit [IsNoetherian X] in
/-- The complex `𝓕[-p]`, a coherent module placed in degree `p`, has coherent terms. -/
public lemma isCoherent_single_X (F : X.Modules) [F.IsCoherent] (p i : ℤ) :
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F).X i).IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  by_cases h : i = p
  · subst h
    exact P.prop_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i F).symm
      (inferInstanceAs F.IsCoherent)
  · exact P.prop_of_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) p F i h)

/-- **The base case of [Stacks, Tag 0G4S], (2) ⇒ (1).** Let `(G_n)` be an inverse system of
`D^b_{Coh}(𝒪_X)` whose image in `D(𝒪_X)` is a system `(S_n)` of `𝒪_X`-modules placed in degree
`p`. If `(S_n)` is pro-isomorphic to `(𝓘^n𝓕)` for a coherent module `𝓕` and an ideal sheaf `𝓘`
cutting out `X ∖ U`, then `(G_n)` is pro-isomorphic to the Deligne system `(𝓘^n𝓕[-p])`.

The Deligne system of the complex `𝓕[-p]` is concentrated in degree `p`, so it is isomorphic to its
one-degree truncation in that degree, which is pro-isomorphic to `(𝓘^n H^p(𝓕[-p]))[-p]` by the
source presentation `AlgebraicGeometry.DeligneSystem.nonempty_proIso_truncGELE_system`; and
`H^p(𝓕[-p]) ≅ 𝓕`. A pro-isomorphism between the images in `D(𝒪_X)` is one in
`D^b_{Coh}(𝒪_X)`, the inclusion being fully faithful. -/
public theorem exists_proIso_of_single (G : ℕᵒᵖ ⥤ BoundedCoherentDerived X) (p : ℤ)
    (S : ℕᵒᵖ ⥤ X.Modules)
    (eG : G ⋙ (boundedCoherentDerived X).ι ≅ S ⋙ DerivedCategory.singleFunctor X.Modules p)
    (I : X.IdealSheafData) (hI : (I.support : Set X) = (Set.range j.base)ᶜ) (F : X.Modules)
    [F.IsCoherent] (e : ProIso S (Stacks.Duality.idealPowerSystem I F)) :
    ProIsoDeligneSystem j G := by
  let C := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F
  have hCGE : CochainComplex.IsStrictlyGE C p := inferInstanceAs _
  have hCLE : CochainComplex.IsStrictlyLE C p := inferInstanceAs _
  let D : DeligneSystem j :=
    DeligneTriangle.deligneSystemOfComplex j I hI C ⟨p, hCGE⟩ ⟨p, hCLE⟩ (isCoherent_single_X F p)
  have hGE : ∀ n, (boundedCoherentTStructure X).IsGE (D.system.obj n) p :=
    D.isGE_system_obj p (D.isStrictlyGE_powers_complex p hCGE)
  have hLE : ∀ n, (boundedCoherentTStructure X).IsLE (D.system.obj n) p :=
    D.isLE_system_obj p (D.isStrictlyLE_powers_complex p hCLE)
  obtain ⟨e₃⟩ := Stacks.Duality.nonempty_proIso_idealPowerSystem (I := I) (J := I) rfl
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) p F).symm
  obtain ⟨e₄⟩ := D.nonempty_proIso_truncGELE_system p
  refine ⟨D, ⟨ProSeq.isoOfProIso (ProIso.ofFullyFaithful
    (boundedCoherentDerived X).fullyFaithfulι ?_)⟩⟩
  exact Pro.proIsoTrans (Pro.proIsoOfNatIso eG) <|
    Pro.proIsoTrans (Pro.proIsoWhiskerRight e (DerivedCategory.singleFunctor X.Modules p)) <|
      Pro.proIsoTrans (Pro.proIsoWhiskerRight e₃ (DerivedCategory.singleFunctor X.Modules p)) <|
        Pro.proIsoTrans e₄.symm <| Pro.proIsoOfNatIso <|
          Functor.isoWhiskerRight
            ((boundedCoherentTStructure X).truncGELESelfIso D.system p hGE hLE).symm
            (boundedCoherentDerived X).ι

omit [IsNoetherian X] in
/-- Cohomology in the range `[a, b]` is the degree range `[a, b]` for the `t`-structure of
`D^b_{Coh}(𝒪_X)`: lower bound. -/
public lemma isGE_of_isZero_homology (L : BoundedCoherentDerived X) (a : ℤ)
    (h : ∀ i < a, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((boundedCoherentDerived X).ι.obj L))) :
    (boundedCoherentTStructure X).IsGE L a :=
  (ObjectProperty.tStructure_isGE_iff (boundedCoherentDerived X) DerivedCategory.TStructure.t
    L a).mpr ((DerivedCategory.isGE_iff _ a).mpr h)

omit [IsNoetherian X] in
/-- Cohomology in the range `[a, b]` is the degree range `[a, b]` for the `t`-structure of
`D^b_{Coh}(𝒪_X)`: upper bound. -/
public lemma isLE_of_isZero_homology (L : BoundedCoherentDerived X) (b : ℤ)
    (h : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((boundedCoherentDerived X).ι.obj L))) :
    (boundedCoherentTStructure X).IsLE L b :=
  (ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived X) DerivedCategory.TStructure.t
    L b).mpr ((DerivedCategory.isLE_iff _ b).mpr h)

/-- **[Stacks, Tag 0G4S], (2) ⇒ (1).** Let `(K_n)` be an inverse system of `D^b_{Coh}(𝒪_X)` with
`H^i(K_n) = 0` for `i ∉ [a, b]`, and `𝓘` a quasi-coherent sheaf of ideals cutting out `X ∖ U`. If
for every `p` the system `(H^p(K_n))` is pro-isomorphic to `(𝓘^n𝓕)` for a coherent `𝓕`, then
`(K_n)` is pro-isomorphic to a Deligne system.

The source's induction on `b - a` along the truncation triangles is
`CategoryTheory.Triangulated.TStructure.prop_of_truncGELE`, with two out of three supplied by
[Stacks, Tag 0G4Q] (`AlgebraicGeometry.DeligneSystem.proIsoDeligneSystem_π₂`) and the base case
by `AlgebraicGeometry.DeligneSystem.exists_proIso_of_single`, the one-degree truncation in
degree `p` being `H^p(K_n)` placed in degree `p`
(`AlgebraicGeometry.truncGELECompιIsoSingleFunctor`). -/
public theorem proIsoDeligneSystem_of_homology (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range j.base)ᶜ) {a b : ℤ}
    (hab : a ≤ b) (K : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hK : ∀ (n : ℕ) (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((boundedCoherentDerived X).ι.obj (K.obj (op n)))))
    (H : ∀ p : ℤ, ∃ F : X.Modules, F.IsCoherent ∧
      Nonempty (ProSeq.of ((K ⋙ (boundedCoherentDerived X).ι) ⋙
        DerivedCategory.homologyFunctor X.Modules p) ≅
          ProSeq.of (Stacks.Duality.idealPowerSystem I F))) :
    ProIsoDeligneSystem j K := by
  refine (boundedCoherentTStructure X).prop_of_truncGELE (ProIsoDeligneSystem j)
    ProIsoDeligneSystem.of_natIso proIsoDeligneSystem_π₂ hab K
    (fun n => isGE_of_isZero_homology _ a fun i hi => hK n.unop i (Or.inl hi))
    (fun n => isLE_of_isZero_homology _ b fun i hi => hK n.unop i (Or.inr hi))
    (fun p _ _ => ?_)
  obtain ⟨F, hF, ⟨e⟩⟩ := H p
  exact exists_proIso_of_single (K ⋙ (boundedCoherentTStructure X).truncGELE p p) p _
    (truncGELECompιIsoSingleFunctor K p) I hI F (ProSeq.proIsoOfIso e)

/-- **Stacks Project, Tag 0G4S.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes and
`𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals with `V(𝓘) = X ∖ U`. Let `a ≤ b` be integers and
`(K_n)` an inverse system of `D^b_{Coh}(𝒪_X)` such that `H^i(K_n) = 0` for `i ∉ [a, b]`. The
following are equivalent:

1. `(K_n)` is pro-isomorphic to a Deligne system;
2. for every `p ∈ ℤ` there exists a coherent `𝒪_X`-module `𝓕` such that the pro-systems
   `(H^p(K_n))` and `(𝓘^n𝓕)` are pro-isomorphic.

(1) ⇒ (2) is `AlgebraicGeometry.DeligneSystem.exists_proIso_homology_of_proIso`, from
[Stacks, Tag 0G4R]; (2) ⇒ (1) is `AlgebraicGeometry.DeligneSystem.proIsoDeligneSystem_of_homology`,
from [Stacks, Tag 0G4Q]. The ideal `𝓘` of (2) is any one cutting out `X ∖ U`. -/
@[stacks 0G4S]
public theorem proIsoDeligneSystem_iff_homology (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range j.base)ᶜ) {a b : ℤ}
    (hab : a ≤ b) (K : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hK : ∀ (n : ℕ) (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((boundedCoherentDerived X).ι.obj (K.obj (op n))))) :
    ProIsoDeligneSystem j K ↔
      ∀ p : ℤ, ∃ F : X.Modules, F.IsCoherent ∧
        Nonempty (ProSeq.of ((K ⋙ (boundedCoherentDerived X).ι) ⋙
          DerivedCategory.homologyFunctor X.Modules p) ≅
            ProSeq.of (Stacks.Duality.idealPowerSystem I F)) :=
  ⟨exists_proIso_homology_of_proIso I hI K,
    proIsoDeligneSystem_of_homology I hI hab K hK⟩

end AlgebraicGeometry.DeligneSystem

end
