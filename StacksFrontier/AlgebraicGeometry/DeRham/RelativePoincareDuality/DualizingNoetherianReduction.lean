module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRigidity
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperSmoothRelativeDimension

/-!
# `Ω^d_{X/S}[d] ≅ a(𝒪_S)` over a general base, from the Noetherian case

Let `f : X ⟶ S` be proper and smooth of relative dimension `d`, with `S` quasi-compact and
quasi-separated, and let `a` be the twisted inverse image of `f` ([Stacks, Tag 0A9E]). The
isomorphism `Ω^d_{X/S}[d] ≅ a(𝒪_S)` of [Stacks, Tag 0BRT] is stated over a Noetherian base. It
descends to the general base: by Noetherian approximation `f` is the base change of a proper
smooth morphism `h : Y ⟶ T` of relative dimension `d` with `T` Noetherian, along some
`q : S ⟶ T`. Then

`Ω^d_{X/S}[d] ≅ L(q')^*(Ω^d_{Y/T}[d]) ≅ L(q')^* a_h(𝒪_T) ≅ a_f(Lq^*𝒪_T) ≅ a_f(𝒪_S)`,

by base change for differential forms ([Stacks, Tag 0FL5]) and the K-flatness of a locally free
sheaf, the Noetherian case, flat base change for the twisted inverse image of a proper flat
morphism of finite presentation ([Stacks, Tag 0AAB]), and `Lq^*𝒪_T ≅ 𝒪_S`.

The Noetherian case enters as the hypothesis `H` of
`Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian`,
in the statement shape of `Stacks.Duality.singleFunctorExteriorPowerIsoRelativeDualizingComplex`.

## Main results

* `Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_isPullback`
* `Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X Y S T : Scheme.{u}} {q' : X ⟶ Y} {f : X ⟶ S} {h : Y ⟶ T} {q : S ⟶ T}
  [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]

/-- **`Ω^d[d] ≅ a(𝒪)` is stable under base change.** In a cartesian square with `h : Y ⟶ T`
proper and smooth of relative dimension `d`, an isomorphism `Ω^d_{Y/T}[d] ≅ a_h(𝒪_T)` gives one
`Ω^d_{X/S}[d] ≅ a_f(𝒪_S)`, through flat base change for the twisted inverse image
([Stacks, Tag 0AAB]). -/
theorem nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_isPullback
    (sq : IsPullback q' f h q) (d : ℕ) [IsProper h] [SmoothOfRelativeDimension d h]
    [IsProper f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
    haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated h
    ((DerivedCategory.singleFunctor Y.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials h) d) ≅
      (relativeDualizingComplex h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
        (DerivedPushforward.derivedStructureSheaf T)).obj) →
    Nonempty ((DerivedCategory.singleFunctor X.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) ≅
      (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf S)).obj) := by
  intro ψ₀
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated h
  have : Smooth h := SmoothOfRelativeDimension.smooth d h
  have h0 := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat sq
    (DerivedPushforward.derivedStructureSheaf T)
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback q' h f q sq (d : ℤ)
  exact ⟨(DerivedCategory.singleFunctor X.Modules (-d)).mapIso
      (asIso (Scheme.Hom.relativeDifferentialFormsMap q' h f q sq.w (d : ℤ))).symm ≪≫
    (derivedPullbackSingleIsoOfIsFlat q' _
      (ProperSmoothDeRham.isFlat_relativeDifferentialForms h d) (-d)).symm ≪≫
    (derivedPullback q').mapIso ψ₀ ≪≫
    (ι _).mapIso (@asIso _ _ _ _ _ h0) ≪≫
    (ι _).mapIso ((twistedInverseImage f _).mapIso
      (quasiCoherentDerivedPullbackStructureSheafIso q))⟩

/-- **`Ω^d_{X/S}[d] ≅ a(𝒪_S)` over a quasi-compact quasi-separated base, from the Noetherian
case**: by Noetherian approximation `f` is the base change of a proper smooth morphism of
relative dimension `d` over a Noetherian scheme, to which `H` applies. -/
theorem nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsProper f]
    (H : ∀ {Y T : Scheme.{u}} [IsNoetherian T] (h : Y ⟶ T) [SmoothOfRelativeDimension d h]
      [IsProper h],
      haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
      haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated h
      Nonempty ((DerivedCategory.singleFunctor Y.Modules (-d)).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials h) d) ≅
        (relativeDualizingComplex h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
          (DerivedPushforward.derivedStructureSheaf T)).obj)) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    Nonempty ((DerivedCategory.singleFunctor X.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) ≅
      (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf S)).obj) := by
  obtain ⟨T, Y, h, q, q', hT, hh, hs, sq⟩ :=
    exists_isPullback_isNoetherian_smoothOfRelativeDimension f d
  obtain ⟨ψ₀⟩ := H h
  exact nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_isPullback sq d ψ₀

end Stacks.Duality

end
