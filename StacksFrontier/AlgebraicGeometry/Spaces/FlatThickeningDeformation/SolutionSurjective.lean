module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.KernelCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.SolutionRingedTopos

/-!
# Every solution of the extension problem of a flat morphism comes from a flat deformation

Let `Y ⊂ Y'` be a first-order thickening of algebraic spaces with inclusion `t`, and `f : X ⟶ Y`
flat. This file completes the comparison of the proof of [Stacks Project, Tag 0D17] between flat
deformations of `f` over `Y'` and solutions of the extension problem of
[Stacks Project, Tag 08UF] attached to `f`.

Given a solution `0 → f^*𝒞_{Y/Y'} → 𝒪' → 𝒪_X → 0`, Stacks 05ZT realizes it by a first-order
thickening `X ≅ X₀ ⊂ X'` over `Y'` with `i⁻¹𝒪_{X'} ≅ 𝒪'`
(`nonempty_realization_solutionSquareZeroExtension`). The conormal map
`f₀^*𝒞_{Y/Y'} ⟶ 𝒞_{X₀/X'}` of this thickening is an isomorphism: restricted to `X₀`, the
extension `𝒪_{X'}|_{X₀}` of `𝒪_{X₀}` by `𝒞_{X₀/X'}` is isomorphic, over `𝒪_{X₀}` and under the
thickened base, to the restriction of `𝒪'`, whose kernel is `f₀^*𝒞_{Y/Y'}`; the conormal map
followed by the inclusion of `𝒞_{X₀/X'}` is the ideal image of the base, as is `c` followed by the
inclusion of `f₀^*𝒞_{Y/Y'}`; since `c` is universal (the unit of extension of scalars) the
conormal map is inverse to the map of kernels induced by the isomorphism. Hence, by Stacks 06BH,
`X' ⟶ Y'` is flat and `X = X' ×_{Y'} Y`: a flat deformation, whose solution `i⁻¹𝒪_{X'}` is `𝒪'`.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.isIso_of_iso_extension_of_universal`:
  a map from `𝒢` to the kernel of an extension isomorphic to a solution, compatible with `c`, is
  invertible when `c` is universal.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.isIso_conormalMap_realized`: the conormal map
  of the thickening realizing a solution is an isomorphism.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.classesMap_surjective`,
  `AlgebraicGeometry.Space.FlatThickeningDeformation.classesMap_bijective`: for flat `f`, the map
  from isomorphism classes of flat deformations to isomorphism classes of solutions is bijective.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.classesEquiv`: the resulting bijection.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

section GenericKernel

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

/-- **A map to the kernel of an extension isomorphic to a solution is invertible**, when `c` is
universal. Let `𝒪''` be an extension of `𝒜`-algebras of `𝒪_X` by `𝒩`, isomorphic over `𝒪_X` and
under the thickened base to a solution `𝒪'`, and `κ : 𝒢 ⟶ 𝒩` such that the image in `𝒪''` of a
section `x` of the base ideal is the image of `κ(c(x))`. Then `κ` is an isomorphism: the map
`ψ : 𝒩 ⟶ 𝒢` of kernels induced by `𝒪'' ≅ 𝒪'` is an isomorphism, and `κ ≫ ψ` fixes `c`, so it is
the identity. -/
theorem isIso_of_iso_extension_of_universal (hc : S.CIsUniversal)
    (Q : S.CompatibleFirstOrderThickening) {A₁ : Sheaf X.J CommRingCat.{w}} {a₁ : A₁ ⟶ X.O}
    (θ : A₁ ≅ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
    {N : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (F : Deformation.AlgebraExtension a₁ N) (κ : S.G ⟶ N)
    (hκ : ∀ (U : X.Cᵒᵖ) (x : S.I.val.obj U),
      S.idealImage θ F x = F.incl (κ.val.app U (S.c.val.app U x)))
    (φ : F.extension ≅ Q.extension) (hr : φ.hom ≫ Q.reduction = F.reduction)
    (hb : θ.inv ≫ F.algebraMap ≫ φ.hom = Q.baseMap) : IsIso κ := by
  let a₀ := (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
    S.f.fSharpInverseImage
  let Q' := S.toAlgebraExtension (Iso.refl _) (Category.id_comp a₀) Q
  have hr' : φ.inv ≫ F.reduction = Q'.reduction := φ.inv_comp_eq.2 hr.symm
  let ψ := Deformation.AlgebraExtension.inducedKernelMap F Q' φ.hom hr
  let ψ' := Deformation.AlgebraExtension.inducedKernelMap Q' F φ.inv hr'
  have h1 : ψ ≫ ψ' = 𝟙 N := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun n => F.incl_injective ?_))
    have e1 := Deformation.AlgebraExtension.hom_incl Q' F φ.inv hr' (ψ.val.app U n)
    have e2 := Deformation.AlgebraExtension.hom_incl F Q' φ.hom hr n
    refine e1.symm.trans ((congrArg (φ.inv.hom.app U) e2.symm).trans ?_)
    exact congrArg (fun k : F.extension ⟶ F.extension => k.hom.app U (F.incl n)) φ.hom_inv_id
  have h3 : κ ≫ ψ = 𝟙 S.G := by
    refine hc _ (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => Q'.incl_injective ?_)))
    have e2 := Deformation.AlgebraExtension.hom_incl F Q' φ.hom hr
      (κ.val.app U (S.c.val.app U x))
    have e3 := congrArg (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶
        Q.extension => k.hom.app U
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U x)) hb
    refine e2.symm.trans ((congrArg (φ.hom.hom.app U) (hκ U x).symm).trans ?_)
    exact e3.trans (Q.baseMap_ideal U x)
  refine ⟨ψ, h3, ?_⟩
  calc ψ ≫ κ = ψ ≫ (κ ≫ ψ) ≫ ψ' := by
        rw [Category.assoc, h1, Category.comp_id]
    _ = 𝟙 N := by rw [h3, Category.id_comp, h1]

end Deformation.ToposThickening.RingedToposExtensionProblem

section GenericFactorization

open Deformation Deformation.ToposThickening AlgebraicGeometry

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {D : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [D.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  (f : RingedToposHom X D) {A : Sheaf D.J CommRingCat.{w₂}} {a : A ⟶ D.O}
  {M : SheafOfModules.{w₂} ((sheafCompose D.J (forget₂ CommRingCat.{w₂} RingCat.{w₂})).obj D.O)}
  (E : AlgebraExtension a M)
  (G : SheafOfModules.{w₁} ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj X.O))
  (c : inverseImageExtensionIdeal f (M := M) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).map
          f.fSharpInverseImage)).obj G)
  {A₁ : Sheaf X.J CommRingCat.{w₁}} {a₁ : A₁ ⟶ X.O}
  (θ : A₁ ≅ (inverseImageCommRingFunctor f.toToposHom).obj E.extension)
  {N : SheafOfModules.{w₁} ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj X.O)}

/-- **The ideal image from a factorization through the kernel**, on sections: if the ideal image
map `f⁻¹𝒥 ⟶ 𝒜 ⟶ 𝒪'` is, on underlying sheaves of sets, `c` followed by a map `φ : 𝒢 ⟶ 𝒩` and
the inclusion of the kernel `𝒩` of `𝒪'`, then the image of a section `x` is the image of
`φ(c(x))`. (No invertibility of `φ` is needed, unlike for
`isCompatible_transportKernel_of_factorization`.) -/
theorem idealImage_ofBaseAlgebraExtension_of_factorization (Q₀ : AlgebraExtension a₁ N)
    (φ : G ⟶ N)
    (cS : f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose D.J
          (forget₂ CommRingCat.{w₂} RingCat.{w₂})).map E.reduction)).obj M)) ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj G)
    (φS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj G ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj N)
    (ιS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj N ⟶ X.forgetRing.obj Q₀.extension)
    (h : f.toToposHom.inverseImage.map E.inclSheafSets ≫ X.forgetRing.map (θ.inv ≫ Q₀.algebraMap) =
      cS ≫ φS ≫ ιS)
    (hc : ∀ (U : X.Cᵒᵖ) (x : (inverseImageExtensionIdeal f (M := M)).val.obj U),
      (Sheaf.sectionsFunctor X.J U).map cS x = c.val.app U x)
    (hφ : ∀ (U : X.Cᵒᵖ) (m : G.val.obj U), (Sheaf.sectionsFunctor X.J U).map φS m = φ.val.app U m)
    (hι : ∀ (U : X.Cᵒᵖ) (m : N.val.obj U), (Sheaf.sectionsFunctor X.J U).map ιS m = Q₀.incl m)
    (U : X.Cᵒᵖ) (x : (inverseImageExtensionIdeal f (M := M)).val.obj U) :
    (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c).idealImage θ Q₀ x =
      Q₀.incl (φ.val.app U (c.val.app U x)) :=
  (idealImage_ofBaseAlgebraExtension f E G c θ Q₀ U x).trans
    ((congrArg (fun ψ ↦ (Sheaf.sectionsFunctor X.J U).map ψ x) h).trans
      ((congrArg (fun y ↦ (Sheaf.sectionsFunctor X.J U).map ιS y)
        ((hφ U _).trans (congrArg (φ.val.app U) (hc U x)))).trans (hι U _)))

/-- **A map from `𝒢` to the kernel of an extension isomorphic to a solution is invertible**, for
a problem posed by `ofBaseAlgebraExtension` with universal `c`, when the ideal image of the
extension factors, on underlying sheaves of sets, as `c`, the map, and the inclusion of the kernel
(`idealImage_ofBaseAlgebraExtension_of_factorization` and
`isIso_of_iso_extension_of_universal`). -/
theorem isIso_of_factorization_of_iso_extension
    (hcu : (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c).CIsUniversal)
    (Q : RingedToposExtensionProblem.CompatibleFirstOrderThickening
      (RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c))
    (F : AlgebraExtension a₁ N) (κ : G ⟶ N)
    (cS : f.toToposHom.inverseImage.obj (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose D.J
          (forget₂ CommRingCat.{w₂} RingCat.{w₂})).map E.reduction)).obj M)) ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj G)
    (φS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj G ⟶
      (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
          X.O)).obj N)
    (ιS : (Sheaf.moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w₁} RingCat.{w₁})).obj
        X.O)).obj N ⟶ X.forgetRing.obj F.extension)
    (h : f.toToposHom.inverseImage.map E.inclSheafSets ≫ X.forgetRing.map (θ.inv ≫ F.algebraMap) =
      cS ≫ φS ≫ ιS)
    (hc : ∀ (U : X.Cᵒᵖ) (x : (inverseImageExtensionIdeal f (M := M)).val.obj U),
      (Sheaf.sectionsFunctor X.J U).map cS x = c.val.app U x)
    (hφ : ∀ (U : X.Cᵒᵖ) (m : G.val.obj U), (Sheaf.sectionsFunctor X.J U).map φS m = κ.val.app U m)
    (hι : ∀ (U : X.Cᵒᵖ) (m : N.val.obj U), (Sheaf.sectionsFunctor X.J U).map ιS m = F.incl m)
    (φ : F.extension ≅ Q.extension) (hr : φ.hom ≫ Q.reduction = F.reduction)
    (hb : θ.inv ≫ F.algebraMap ≫ φ.hom = Q.baseMap) : IsIso κ :=
  RingedToposExtensionProblem.isIso_of_iso_extension_of_universal hcu Q θ F κ
    (idealImage_ofBaseAlgebraExtension_of_factorization f E G c θ F κ cS φS ιS h hc hφ hι) φ hr hb

end GenericFactorization

end GenericKernel

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem
open Stacks.Sheaves.ToposPushforward

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  {hZ : IsFirstOrderThickening B S hS Y' Z.1} {X : AlgebraicSpaces B S hS}
  {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}
  {P : (problem f hZ).CompatibleFirstOrderThickening}
  (r : SquareZeroExtension.Realization B S hS (solutionSquareZeroExtension P))

/-- A composite through a functor, computed from a factorization (categorical helper). -/
theorem eqToHom_comp_map_comp_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (R : 𝒟 ⥤ 𝒞)
    {A A' O₀ : 𝒞} {E P O : 𝒟} (e : A = A') (a : A' ⟶ R.obj E) (s : E ⟶ P) (red : P ⟶ O)
    (w : R.obj O ⟶ O₀) (sh : E ⟶ O) (hs : s ≫ red = sh) (x : A ⟶ O₀)
    (ha : eqToHom e ≫ a ≫ R.map sh ≫ w = x) :
    (eqToHom e ≫ a ≫ R.map s) ≫ (R.map red ≫ w) = x := by
  subst hs ha
  simp

/-- Assembling the comparison of the maps from the thickened base along `X₀ ≅ X` from the
coherence of the two transports (categorical helper). -/
theorem baseMap_assemble_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (R : 𝒟 ⥤ 𝒞)
    {A A₁ A₂ A₃ N₀ N₁ : 𝒞} {T' U' V' W' N' E : 𝒟} (b : A = A) (k₁ : A ⟶ A₁) (k₂ : A₁ ⟶ A₂)
    (k₃ : A₂ ⟶ A₃) (k₄ : A₃ ⟶ N₀) (e : N₀ = N₁) (x : N₁ ≅ R.obj N') (y : A ⟶ R.obj T')
    (m₁ : T' ⟶ U') (m₂ : U' ⟶ V') (m₃ : V' ⟶ W') (m₄ : W' ⟶ N') (sh : N' ⟶ E) (K : A ⟶ N₁)
    (hC : y ≫ R.map ((m₁ ≫ m₂) ≫ m₃ ≫ m₄) ≫ x.inv = K)
    (hT : eqToHom b ≫ (k₁ ≫ k₂ ≫ k₃ ≫ k₄) ≫ eqToHom e = K) :
    (k₁ ≫ k₂) ≫ (k₃ ≫ k₄) ≫ eqToHom e ≫ x.hom ≫ R.map sh =
      y ≫ R.map (m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ sh) := by
  have h : (k₁ ≫ k₂) ≫ (k₃ ≫ k₄) ≫ eqToHom e = y ≫ R.map ((m₁ ≫ m₂) ≫ m₃ ≫ m₄) ≫ x.inv := by
    rw [hC, ← hT, eqToHom_refl]
    simp only [Category.assoc, Category.id_comp]
  simp only [Category.assoc] at h ⊢
  rw [reassoc_of% h]
  simp

/-- The inclusion `X₀ ⊂ X'` of a realization is `X₀ ≅ X` followed by its immersion. -/
theorem realizedIso_inv_comp_immersion :
    (realizedIso r).inv ≫ r.immersion =
      subspaceInclusion B S hS r.ambient (realizedSubspace r) := by
  rw [← realizedIso_hom_comp_subspaceInclusion r, Iso.inv_hom_id_assoc]

/-- The solution `P` of the problem of `f`, restricted along `X₀ ≅ X` to a solution of the problem
of `f₀ : X₀ ⟶ Y`. -/
abbrev realizedFibreSolution :
    (problem (realizedReduction r) hZ).CompatibleFirstOrderThickening :=
  fibreSolution hZ (realizedIso r).symm f P

/-- `ι⁻¹𝒪_{X'} ≅ 𝒪'|_{X₀}` for the inclusion `ι : X₀ ⊂ X'` of a realization: the composition law
of inverse images along `X₀ ≅ X ⟶ X'`, with étale restriction along `X₀ ≅ X`, followed by the
restriction of `i⁻¹𝒪_{X'} ≅ 𝒪'`. -/
def realizedExtensionIso :
    inverseImageStructureSheaf B S hS (subspaceInclusion B S hS r.ambient (realizedSubspace r)) ≅
      (realizedFibreSolution r).extension :=
  eqToIso (congrArg (inverseImageStructureSheaf B S hS) (realizedIso_inv_comp_immersion r).symm) ≪≫
    fibreRingIso (realizedIso r).symm r.immersion (smallEtaleRingedTopos B S hS r.ambient).O ≪≫
    (fibreRingRes (realizedIso r).symm).mapIso r.sheafIso

/-- The forward map of `realizedExtensionIso` is the composite of its three constituent maps. -/
theorem realizedExtensionIso_hom :
    (realizedExtensionIso r).hom =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS)
          (realizedIso_inv_comp_immersion r).symm) ≫
        (fibreRingIso (realizedIso r).symm r.immersion
          (smallEtaleRingedTopos B S hS r.ambient).O).hom ≫
          (fibreRingRes (realizedIso r).symm).map r.sheafIso.hom :=
  rfl

/-- `realizedExtensionIso` is over `𝒪_{X₀}`. -/
theorem realizedExtensionIso_hom_comp_reduction :
    (realizedExtensionIso r).hom ≫ (realizedFibreSolution r).reduction =
      structureSharpInverseImage B S hS
        (subspaceInclusion B S hS r.ambient (realizedSubspace r)) := by
  have hq : r.sheafIso.hom ≫ P.reduction = structureSharpInverseImage B S hS r.immersion :=
    r.quotient_compatibility
  rw [fibreSolution_reduction, realizedExtensionIso_hom]
  have hs := (congrArg (eqToHom (congrArg (inverseImageStructureSheaf B S hS)
      (realizedIso_inv_comp_immersion r).symm) ≫ ·) (fibreRingIso_hom_comp_structureSharp
        (realizedIso r).symm r.immersion)).trans
    (structureSharpInverseImage_eqToHom B S hS (realizedIso_inv_comp_immersion r).symm)
  exact eqToHom_comp_map_comp_aux (fibreRingRes (realizedIso r).symm) _ _ _ _ _ _ hq _ hs

/-- The base map of a solution `P` is the isomorphism from `f` followed by the structure map of its
realization (`Realization.algebra_compatibility_eqToHom`, solved for `P.baseMap`). -/
private theorem baseMap_eq_realization :
    P.baseMap =
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f
          (subspaceInclusion B S hS Y' Z)).app (smallEtaleRingedTopos B S hS Y').O).hom ≫
        eqToHom (congrArg (fun φ ↦ (smallEtaleInverseImageRing B S hS φ).obj
          (smallEtaleRingedTopos B S hS Y').O) r.over_base.symm) ≫
          (smallEtaleRingedToposHom_compInverseImageRingIso B S hS r.immersion r.toBase).inv.app
              (smallEtaleRingedTopos B S hS Y').O ≫
            (smallEtaleInverseImageRing B S hS r.immersion).map
                (smallEtaleRingedToposHom B S hS r.toBase).fSharpInverseImage ≫
              r.sheafIso.hom :=
  (Iso.inv_comp_eq ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f
    (subspaceInclusion B S hS Y' Z)).app (smallEtaleRingedTopos B S hS Y').O)).1
      r.algebra_compatibility_eqToHom

/-- `realizedExtensionIso` is under the thickened base: the structure map of the first-order
thickening `X₀ ⊂ X'` over `Y'` corresponds to the base map of `P` restricted to `X₀`. -/
theorem squareBaseIso_inv_comp_realizedExtensionIso_hom :
    (squareBaseIso hZ (realizedSubspace r) r.toBase (realizedReduction r) (realized_comm r)).inv ≫
        (firstOrderAlgebraExtension B S hS (realizedSubspace r) r.firstOrder r.toBase).algebraMap ≫
          (realizedExtensionIso r).hom =
      (realizedFibreSolution r).baseMap := by
  have hP := baseMap_eq_realization r
  have hC := fibreRingIso_squareBaseIso_coherence (incl := r.immersion) (g := r.toBase) (e₀ := f)
    (t := subspaceInclusion B S hS Y' Z) (hsq := r.over_base) (ρ := (realizedIso r).symm)
  have hT := baseMap_transport (g := r.toBase) (t := subspaceInclusion B S hS Y' Z)
    (f₁ := realizedReduction r) (f₂ := realizedReduction r) rfl
    (realizedIso_inv_comp_immersion r).symm (realized_comm r).symm
    (by simp only [realizedReduction, Category.assoc, r.over_base]) rfl
    (inverseImage_congr (realizedIso_inv_comp_immersion r).symm
      (smallEtaleRingedTopos B S hS r.ambient).O)
  have h := baseMap_assemble_aux (fibreRingRes (realizedIso r).symm) _ _ _ _ _
    (congrArg (inverseImageStructureSheaf B S hS) (realizedIso_inv_comp_immersion r).symm)
    (fibreRingIso (realizedIso r).symm r.immersion (smallEtaleRingedTopos B S hS r.ambient).O)
    _ _ _ _ _ r.sheafIso.hom _ hC hT
  have e1 := congrArg (fun k => (fibreRingIso (realizedIso r).symm f
    (baseExtension hZ).extension).hom ≫ (fibreRingRes (realizedIso r).symm).map k) hP
  exact (h.trans e1.symm).trans (fibreSolution_baseMap hZ (realizedIso r).symm f P).symm

/-- **The conormal map of a realized thickening is an isomorphism.** For the thickening
`X₀ ⊂ X'` realizing a solution `P` of the problem of `f`, the map `f₀^*𝒞_{Y/Y'} ⟶ 𝒞_{X₀/X'}` is
invertible: `𝒪_{X'}|_{X₀}` is isomorphic over `𝒪_{X₀}` and under the thickened base to the
restriction of `P`, whose kernel is `f₀^*𝒞_{Y/Y'}`, and the conormal map is compatible with the
prescribed map `c` (`idealImageSets_eq_firstOrderAlgebraMap`), which is universal. -/
theorem isIso_conormalMap_realized :
    IsIso (conormalMap B S hS (realizedSubspace r) Z r.toBase (realizedReduction r)
      (realized_comm r)) :=
  isIso_of_factorization_of_iso_extension (smallEtaleRingedToposHom B S hS (realizedReduction r))
    (baseExtension hZ) (pulledBackConormal (realizedReduction r))
    (problem (realizedReduction r) hZ).c
    (squareBaseIso hZ (realizedSubspace r) r.toBase (realizedReduction r) (realized_comm r))
    (cIsUniversal_problem hZ (realizedReduction r)) (realizedFibreSolution r)
    (firstOrderAlgebraExtension B S hS (realizedSubspace r) r.firstOrder r.toBase)
    (conormalMap B S hS (realizedSubspace r) Z r.toBase (realizedReduction r) (realized_comm r))
    (problemCSets hZ (realizedSubspace r) (realizedReduction r)) _
    (conormalSetInclusion B S hS (realizedSubspace r) r.firstOrder)
    (idealImageSets_eq_firstOrderAlgebraMap hZ (realizedSubspace r) r.firstOrder r.toBase
      (realizedReduction r) (realized_comm r))
    (problemCSets_sections hZ (realizedSubspace r) (realizedReduction r))
    (sections_conormalMap (realizedSubspace r) r.toBase (realizedReduction r) (realized_comm r))
    (sections_conormalSetInclusion (realizedSubspace r) r.firstOrder r.toBase)
    (realizedExtensionIso r) (realizedExtensionIso_hom_comp_reduction r)
    (squareBaseIso_inv_comp_realizedExtensionIso_hom r)

/-- Reassociating a composite through an `eqToHom` (categorical helper). -/
theorem comp_eqToHom_comp_assoc_aux {𝒞 : Type*} [Category 𝒞] {A₀ A B C₀ D₀ E₀ : 𝒞}
    (a : A₀ ⟶ A) (p q : A = B) (c : B ⟶ C₀) (d : C₀ ⟶ D₀) (s : D₀ ⟶ E₀) :
    (a ≫ eqToHom p ≫ c ≫ d) ≫ s = a ≫ eqToHom q ≫ c ≫ d ≫ s := by
  simp

/-- **The flat deformation realizing a solution** (Stacks 06BH, (2) ⟹ (1)): for flat `f`, the
thickening `X ⊂ X'` over `Y'` realizing a solution `P` is a flat deformation of `f`, its conormal
map being invertible (`isIso_conormalMap_realized`). -/
def realizedDeformation (hf : IsFlat B S hS f.hom) : Deformation f :=
  deformationOfIsIsoConormalMap r hf (isIso_conormalMap_realized r)

/-- The closed immersion of the realized deformation is the immersion of the realization. -/
theorem realizedDeformation_i (hf : IsFlat B S hS f.hom) :
    (realizedDeformation r hf).i = r.immersion :=
  rfl

/-- **The realized deformation gives back the solution**: its solution `i⁻¹𝒪_{X'}` is isomorphic
to `P` along `i⁻¹𝒪_{X'} ≅ 𝒪'`, which is over `𝒪_X` and under the thickened base by construction of
the realization; the prescribed map `c` being universal, it is an isomorphism of solutions. -/
theorem isomorphic_ambientSolution_realizedDeformation (hf : IsFlat B S hS f.hom) :
    CompatibleFirstOrderThickening.Isomorphic.{u, u + 1, u, u, u + 1, u}
      ((realizedDeformation r hf).ambientSolution hZ) P := by
  have hP := baseMap_eq_realization r
  refine isomorphic_of_hom_of_universal (cIsUniversal_problem hZ f) r.sheafIso.hom ?_ ?_
  · rw [Deformation.ambientSolution_reduction]
    exact r.quotient_compatibility
  · refine ((congrArg (· ≫ r.sheafIso.hom)
      (Deformation.ambientSolution_baseMap hZ (realizedDeformation r hf))).trans ?_).trans hP.symm
    exact comp_eqToHom_comp_assoc_aux _ _ _ _ _ _

section Bijective

variable (hZ) (f)

/-- **Every solution comes from a flat deformation**: for flat `f`, the map from isomorphism
classes of flat deformations of `f` over `Y'` to isomorphism classes of solutions of the
extension problem attached to `f` is surjective. A solution `P` is a square-zero extension over
`f ≫ t` with ideal pulled back from `Y ⊂ Y'`, realized by a thickening `X ⊂ X'` over `Y'`
(Stacks 05ZT), which is a flat deformation (Stacks 06BH) whose solution is isomorphic to `P`. -/
theorem classesMap_surjective (hf : IsFlat B S hS f.hom) :
    Function.Surjective (classesMap hZ f) := by
  rintro ⟨P⟩
  obtain ⟨r⟩ := nonempty_realization_solutionSquareZeroExtension P
  exact ⟨Quotient.mk _ (realizedDeformation r hf),
    Quotient.sound (isomorphic_ambientSolution_realizedDeformation r hf)⟩

/-- **The deformations of a flat morphism over a first-order thickening are the solutions of
its extension problem**: for flat `f : X ⟶ Y` and a first-order thickening `Y ⊂ Y'`, the map
`[D] ↦ [0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0]` from isomorphism classes of flat deformations of
`f` over `Y'` to isomorphism classes of solutions of the extension problem attached to `f` is a
bijection (the comparison step of the proof of Stacks 0D17). -/
theorem classesMap_bijective (hf : IsFlat B S hS f.hom) :
    Function.Bijective (classesMap hZ f) :=
  ⟨classesMap_injective hZ f, classesMap_surjective hZ f hf⟩

/-- **The bijection between isomorphism classes of flat deformations and of solutions**, for
flat `f` (`classesMap_bijective`). -/
def classesEquiv (hf : IsFlat B S hS f.hom) :
    Classes f ≃ CompatibleFirstOrderThickening.IsomorphismClasses.{u, u + 1, u, u, u + 1, u}
      (problem f hZ) :=
  Equiv.ofBijective _ (classesMap_bijective hZ f hf)

/-- The bijection `classesEquiv` sends a class of deformations to its image under `classesMap`. -/
theorem classesEquiv_apply (hf : IsFlat B S hS f.hom) (D : Classes f) :
    classesEquiv hZ f hf D = classesMap hZ f D :=
  rfl

end Bijective

end AlgebraicGeometry.Space.FlatThickeningDeformation
