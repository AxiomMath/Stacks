module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecPuncturedConeFunctorial
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedMul
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleStructureMorphism
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Contraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationCoproductSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
import StacksCore.Tactic.StacksAttribute

/-!
# The `A`-module structure of `RΓ(U, 𝓕_U) = ⨁_m RΓ(P, 𝓕(m))`

Let `A` be a nonnegatively graded ring, `X = Spec A`, `P = Proj A` quasi-compact, `π : L ⟶ P` the
cone of the truncation algebra and `U ⊆ L` the punctured cone, identified with the open
`X ∖ V(A₊)` of `X`. For a quasi-coherent `𝒪_P`-module `𝓕` the decomposition

  `RΓ(U, 𝓕_U) = ⨁_{m ∈ ℤ} RΓ(P, 𝓕 ⊗_{𝒪_P} 𝒪_P(m))`

of [Stacks, Tag 0EKH] carries two `A`-module structures: on the left the one coming from
`U ⊆ X`, through which `a ∈ A` acts by multiplication by the function it defines on `U`; on the
right the graded one, in which a homogeneous `a ∈ A_k` sends `RΓ(P, 𝓕(m))` to `RΓ(P, 𝓕(k + m))`
through multiplication `𝓕(m) ⟶ 𝓕(k + m)` by the section `a` of `𝒪_P(k)`. The source states that
the decomposition identifies the two; this file proves it.

The argument follows the decomposition through its pieces. On `(π|_U)_*𝒪_U = ⨁_m 𝒪_P(m)` the
function of `a ∈ A_k` restricts, over a standard open `D₊(f)`, to the degree-zero fraction
`σ a / 1` of `(B[1/σ f · ψ f])₀`, and the degreewise inclusions turn multiplication by it into
multiplication by `a` from `𝒪_P(m)` to `𝒪_P(k + m)`
(`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_comp_smul` with
`Stacks.AlgebraicGeometry.ProjConeTwist.ι_puncturedConeStructurePushforwardCoproductIso_inv`).
The projection formula along `π|_U` is natural in the module on `U`, and multiplication by a
function on `𝒪_U ⊗ 𝓕_U` is multiplication on the first factor, so the same holds for
`(π|_U)_*(π|_U)^*𝓕 = ⨁_m 𝓕(m)`
(`Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConePushforwardPullbackCoproductIso_hom_smul`);
`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIso_hom_comp` carries it to
derived global sections
(`Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoOfStructureIso_hom_smul`).

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeFunction`: the function on `U` defined by
  `a ∈ A`, through `U ⊆ X = Spec A`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeSmul`: multiplication by it, on every sheaf
  of modules on `U`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.twistSumSmul`: the graded action of `a ∈ A` on
  `⨁_m RΓ(P, 𝓕(m))`, through the homogeneous components of `a`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_comp_smul`: the degreewise inclusion
  `𝒪_P(m) ⟶ (π|_U)_*𝒪_U` carries multiplication by a homogeneous `a ∈ A_k` to multiplication by
  the function of `a`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation_hom_smul`:
  the decomposition intertwines the two actions of a homogeneous `a ∈ A`.
* `Stacks.AlgebraicGeometry.ProjAndSpec.derivedPushforwardPuncturedConeIsoTruncation_hom_smul_all`:
  **the two `A`-module structures agree**, for every `a ∈ A`.

## Implementation notes

The decomposition is built from identifications stated over two presentations of the structure
sheaf of `P` (`(Proj A).ringCatSheaf` and the sheaf composed from `Proj.structureSheaf`), which
agree definitionally. Checking a statement that crosses between them is expensive for the
kernel, so each lemma here is stated in the presentation of the identification it is about, and
the one fact that has to look inside `(π|_U)_*𝒪_U ≅ ⨁_m 𝒪_P(m)`,
`Stacks.AlgebraicGeometry.ProjConeTwist.ι_puncturedConeStructurePushforwardCoproductIso_inv`, is
read off a general statement about sheafified direct sums,
`Stacks.ι_sheafifyDirectSumIso_inv_comp_sheafifyHomOfPresheafHom`. The pieces are composed for a
general cone, and in the final statement the degreewise multiplication fact is proved directly in
the form the general statement asks for.

## References

* [Stacks Project, Tag 0EKH](https://stacks.math.columbia.edu/tag/0EKH)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v' u' w'

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules TopCat.Sheaf sheafCompose

namespace Stacks.AlgebraicGeometry.ProjAndSpec

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

open Stacks.Duality (derivedPushforward)

/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance ringCatSheafIsMulCommutative (X : Scheme.{u}) :
    ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V => inferInstanceAs (IsMulCommutative (X.presheaf.obj V))

/-- **Multiplication by a global function on `𝒪_X`-modules**, as an endomorphism of the identity
functor of `X.Modules`. -/
def schemeSmul (X : Scheme.{u}) (s : Γ(X, ⊤)) : End (𝟭 X.Modules) :=
  Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop s

/-- **Multiplication by a global function commutes with the left unit constraint**, and on
`𝒪_X ⊗ 𝓜` it is multiplication on the first factor. -/
theorem schemeSmul_comp_tensorSheafLeftUnitor_inv (X : Scheme.{u}) (s : Γ(X, ⊤))
    (M : X.Modules) :
    (schemeSmul X s).asHom.app M ≫
        (Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf X.ringCatSheaf.property M).inv =
      (Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf X.ringCatSheaf.property M).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map
          ((schemeSmul X s).asHom.app (SheafOfModules.unit X.ringCatSheaf))).app M := by
  have : ∀ V, IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ :
        Sheaf (Opens.grothendieckTopology X) CommRingCat)).obj.obj V) :=
    fun V => inferInstanceAs (IsMulCommutative (X.presheaf.obj V))
  have hlu := ((schemeSmul X s).asHom.naturality
    (Stacks.SheafOfModules.tensorSheafLeftUnitor X.presheaf X.ringCatSheaf.property M).inv).symm
  have hT := AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ M
    (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop s)
    (SheafOfModules.unit X.ringCatSheaf)
  exact hlu.trans (whisker_eq _ hT.symm)

/-- Multiplication by the zero function is zero. -/
theorem schemeSmul_zero (X : Scheme.{u}) : schemeSmul X 0 = 0 := by
  change Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop 0 = 0
  ext M V x
  change (ConcreteCategory.hom (X.ringCatSheaf.obj.map (isTerminalTop.from (unop V)).op) 0) • x = 0
  rw [map_zero, zero_smul]

/-- Multiplication by a global function is additive in the function. -/
theorem schemeSmul_add (X : Scheme.{u}) (s t : Γ(X, ⊤)) :
    schemeSmul X (s + t) = schemeSmul X s + schemeSmul X t := by
  change Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop (s + t) =
    Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop s +
      Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop t
  ext M V x
  change (ConcreteCategory.hom (X.ringCatSheaf.obj.map (isTerminalTop.from (unop V)).op) (s + t)) •
      x =
    (ConcreteCategory.hom (X.ringCatSheaf.obj.map (isTerminalTop.from (unop V)).op) s) • x +
      (ConcreteCategory.hom (X.ringCatSheaf.obj.map (isTerminalTop.from (unop V)).op) t) • x
  exact (congrArg (· • x) (map_add (ConcreteCategory.hom
    (X.ringCatSheaf.obj.map (isTerminalTop.from (unop V)).op)) s t)).trans (add_smul _ _ x)

section Cone

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ)

/-- **The function on the punctured cone defined by an element `a ∈ A`**: the pullback of
`a ∈ Γ(X, 𝒪_X)`, `X = Spec A`, along the inclusion `U ⊆ X`. -/
def puncturedConeFunction (a : A) : Γ((openUInL c).toScheme, ⊤) :=
  ((openUInL c).ι ≫ toSpecA c).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

/-- **Multiplication by `a ∈ A` on sheaves of modules on the punctured cone**, through
`puncturedConeFunction`: the `A`-module structure that `U ⊆ X = Spec A` induces, as an
endomorphism of the identity functor. -/
def puncturedConeSmul (a : A) : End (𝟭 (openUInL c).toScheme.Modules) :=
  schemeSmul (openUInL c).toScheme (puncturedConeFunction c a)

/-- **Multiplication by elements of `A` on sheaves of modules on the punctured cone**, as an
additive map `A → End (𝟭 _)`. -/
def puncturedConeSmulAddHom : A →+ End (𝟭 (openUInL c).toScheme.Modules) where
  toFun := puncturedConeSmul c
  map_zero' := by
    have h : puncturedConeFunction c 0 = 0 := by simp only [puncturedConeFunction, map_zero]
    rw [puncturedConeSmul, h, schemeSmul_zero]
  map_add' a b := by
    have h : puncturedConeFunction c (a + b) =
        puncturedConeFunction c a + puncturedConeFunction c b := by
      simp only [puncturedConeFunction, map_add]
    rw [puncturedConeSmul, h, schemeSmul_add]
    rfl

/-- **Multiplication by `a ∈ A` passes through `(π|_U)_*(π|_U)^*𝓕 ≅ ⨁_m 𝓕(m)`.** If, under an
identification `(π|_U)_*𝒪_U ≅ ⨁_m 𝒪_P(m)`, multiplication by `a` on `𝒪_U` becomes the morphism of
direct sums sending the `m`-th summand to the `p m`-th one by `b m`, then multiplication by `a` on
`𝓕_U` becomes the morphism sending `𝓕(m)` to `𝓕(p m)` by `𝓕 ⊗ b m`. -/
theorem puncturedConePushforwardPullbackCoproductIso_hom_smul
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent]
    (h0 : puncturedConeStructurePushforward c ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m)
    (a : A) (p : ℤ → ℤ) (b : ∀ m, twistingSheaf 𝒜 m ⟶ twistingSheaf 𝒜 (p m))
    (φ : ∀ m, twistingSheaf 𝒜 m ⟶ puncturedConeStructurePushforward c)
    (hι : ∀ m, Sigma.ι (fun m : ℤ => twistingSheaf 𝒜 m) m ≫ h0.inv = φ m)
    (hφ : ∀ m, φ m ≫ (Scheme.Modules.pushforward (puncturedConeProj c)).map
          ((puncturedConeSmul c a).asHom.app
            (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)) = b m ≫ φ (p m)) :
    (Scheme.Modules.pushforward (puncturedConeProj c)).map
          ((puncturedConeSmul c a).asHom.app (puncturedConePullback c F) :
            puncturedConePullback c F ⟶ puncturedConePullback c F) ≫
        (puncturedConePushforwardPullbackCoproductIso c F h0).hom =
      (puncturedConePushforwardPullbackCoproductIso c F h0).hom ≫
        Sigma.map' (C := (AlgebraicGeometry.Proj 𝒜).Modules) p
          (fun m => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).obj F).map (b m)) := by
  have : IsAffineHom (puncturedConeProj c) := isAffineHom_pi_restrict c
  have hK0 : (Scheme.Modules.pushforward (puncturedConeProj c)).map
        ((puncturedConeSmul c a).asHom.app
          (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)) ≫ h0.hom =
      h0.hom ≫ Sigma.map' (C := (AlgebraicGeometry.Proj 𝒜).Modules) p b :=
    Glue.hom_square _ _ (Sigma.hom_ext _ _ fun m =>
      ((Sigma.ι_comp_map'_assoc _ _ _ _).trans (whisker_eq _ (hι (p m)))).trans
        ((hφ m).symm.trans ((eq_whisker (hι m) _).symm.trans (Category.assoc _ _ _))))
  have hU := schemeSmul_comp_tensorSheafLeftUnitor_inv (openUInL c).toScheme
    (puncturedConeFunction c a) (puncturedConePullback c F)
  have hPL := projectionFormulaIsoOfQuasicoherent_inv_naturality_left (puncturedConeProj c)
    (G := SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)
    (G' := SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)
    ((puncturedConeSmul c a).asHom.app
      (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)) F
  have hBL := tensorSheafBraiding_hom_naturality_left_proj 𝒜
    ((Scheme.Modules.pushforward (puncturedConeProj c)).map
      ((puncturedConeSmul c a).asHom.app
        (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf))) F
  have hPt := Glue.map_square_comp₂ (Scheme.Modules.pushforward (puncturedConeProj c)) hU hPL hBL
  have hK' := Glue.map_square (projTensorLeft 𝒜 F) hK0
  have hPres := preservesCoproductIso_hom_map' (L := projTensorLeft 𝒜 F) p b
  exact Glue.square_comp₃ hPt hK' hPres

/-- `derivedPushforwardPuncturedConeIso_hom_comp`, with the morphism of direct sums of twists formed
in the category of `𝒪_P`-modules. -/
theorem derivedPushforwardPuncturedConeIso_hom_comp_proj [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    {F G : (AlgebraicGeometry.Proj 𝒜).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : (Scheme.Modules.pushforward (puncturedConeProj c)).obj
        (puncturedConePullback c F) ≅ ∐ fun m : ℤ => twistSheafOfModules 𝒜 F m)
    (hG : (Scheme.Modules.pushforward (puncturedConeProj c)).obj
        (puncturedConePullback c G) ≅ ∐ fun m : ℤ => twistSheafOfModules 𝒜 G m)
    (α : puncturedConePullback c F ⟶ puncturedConePullback c G) (p : ℤ → ℤ)
    (b : ∀ m, twistSheafOfModules 𝒜 F m ⟶ twistSheafOfModules 𝒜 G (p m))
    (h : (Scheme.Modules.pushforward (puncturedConeProj c)).map α ≫ hG.hom =
      hF.hom ≫ Sigma.map' (C := (AlgebraicGeometry.Proj 𝒜).Modules) p b) :
    (derivedPushforward (puncturedConeProj c ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
          ((DerivedCategory.singleFunctor (openUInL c).toScheme.Modules 0).map α) ≫
        (derivedPushforwardPuncturedConeIso c G hG).hom =
      (derivedPushforwardPuncturedConeIso c F hF).hom ≫
        Sigma.map' p (fun m => (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
          ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map (b m))) :=
  derivedPushforwardPuncturedConeIso_hom_comp c hF hG α p b h

/-- **Multiplication by `a ∈ A` on `RΓ(U, 𝓕_U)` passes through
`derivedPushforwardPuncturedConeIsoOfStructureIso`.** If, under an identification
`(π|_U)_*𝒪_U ≅ ⨁_m 𝒪_P(m)` whose inverse is `φ m` on the `m`-th summand, multiplication by `a` on
`𝒪_U` restricts on `𝒪_P(m)` to `b m : 𝒪_P(m) ⟶ 𝒪_P(p m)`, then multiplication by `a` on
`RΓ(U, 𝓕_U)` becomes the morphism of direct sums sending `RΓ(P, 𝓕(m))` to `RΓ(P, 𝓕(p m))` by
`RΓ(P, 𝓕 ⊗ b m)`. -/
theorem derivedPushforwardPuncturedConeIsoOfStructureIso_hom_smul
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent]
    (h0 : puncturedConeStructurePushforward c ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m)
    (a : A) (p : ℤ → ℤ) (b : ∀ m, twistingSheaf 𝒜 m ⟶ twistingSheaf 𝒜 (p m))
    (φ : ∀ m, twistingSheaf 𝒜 m ⟶ puncturedConeStructurePushforward c)
    (hι : ∀ m, Sigma.ι (fun m : ℤ => twistingSheaf 𝒜 m) m ≫ h0.inv = φ m)
    (hφ : ∀ m, φ m ≫ (Scheme.Modules.pushforward (puncturedConeProj c)).map
          ((puncturedConeSmul c a).asHom.app
            (SheafOfModules.unit (openUInL c).toScheme.ringCatSheaf)) = b m ≫ φ (p m)) :
    (derivedPushforward (puncturedConeProj c ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
        ((DerivedCategory.singleFunctor (openUInL c).toScheme.Modules 0).map
          ((puncturedConeSmul c a).asHom.app (puncturedConePullback c F) :
            puncturedConePullback c F ⟶ puncturedConePullback c F)) ≫
        (derivedPushforwardPuncturedConeIsoOfStructureIso c F h0).hom =
      (derivedPushforwardPuncturedConeIsoOfStructureIso c F h0).hom ≫
        Sigma.map' p (fun m =>
          (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
            ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).obj F).map (b m)))) :=
  derivedPushforwardPuncturedConeIso_hom_comp_proj c _ _ _ _ _
    (puncturedConePushforwardPullbackCoproductIso_hom_smul c F h0 a p b φ hι hφ)

end Cone

end Stacks.AlgebraicGeometry.ProjAndSpec

namespace Stacks

section SheafifiedDirectSum

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w'}}
  [HasWeakSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- Two morphisms out of a sheafification agree once they agree after the sheafification unit. -/
theorem sheafification_hom_ext {P : PresheafOfModules.{w'} R.obj} {Q : SheafOfModules.{w'} R}
    {g h : (PresheafOfModules.sheafification (𝟙 R.obj)).obj P ⟶ Q}
    (hgh : (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫
        (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map g =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫
        (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map h) :
    g = h :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).injective
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_unit _ _ _).trans
      (hgh.trans ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_unit _ _ _).symm))

/-- `sheafifyHomOfPresheafHom` is natural in the presheaf it starts from. -/
theorem sheafification_map_comp_sheafifyHomOfPresheafHom {P P' : PresheafOfModules.{w'} R.obj}
    {M : SheafOfModules.{w'} R} (f : P ⟶ P') (c : P' ⟶ M.val) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map f ≫ sheafifyHomOfPresheafHom c =
      sheafifyHomOfPresheafHom (f ≫ c) := by
  refine sheafification_hom_ext ?_
  have u := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f
  refine Eq.trans ?_ (sheafifyUnit_comp_sheafifyHomOfPresheafHom (f ≫ c)).symm
  rw [Functor.map_comp, ← Category.assoc]
  refine (eq_whisker u.symm _).trans ?_
  rw [Category.assoc]
  exact whisker_eq f (sheafifyUnit_comp_sheafifyHomOfPresheafHom c)

/-- `sheafifyHomOfPresheafHom` of the morphism underlying a morphism of sheaves is that morphism,
after the sheafification counit. -/
theorem sheafifyHomOfPresheafHom_val {N M : SheafOfModules.{w'} R} (φ : N ⟶ M) :
    sheafifyHomOfPresheafHom φ.val =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N ≫ φ := by
  have h1 : sheafifyHomOfPresheafHom φ.val =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv N.val M).symm φ.val :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv N.val M).injective
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_unit _ _ _).trans
        (sheafifyUnit_comp_sheafifyHomOfPresheafHom φ.val)).trans
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv N.val M).apply_symm_apply
          φ.val).symm)
  exact h1.trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_counit _ _ _).trans
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality φ))

variable {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{w'} R) [HasCoproduct N]
  {M : SheafOfModules.{w'} R} (φ : ∀ i, N i ⟶ M)

/-- **On the `i`-th summand, the morphism out of the sheafified direct sum induced by a family of
morphisms is the `i`-th member of the family.** -/
theorem ι_sheafifyDirectSumIso_inv_comp_sheafifyHomOfPresheafHom (i : ι) :
    Sigma.ι N i ≫ (sheafifyDirectSumIso N).inv ≫
        sheafifyHomOfPresheafHom (directSumDesc (fun j => (N j).val) fun j => (φ j).val) =
      φ i := by
  rw [reassoc_of% (ι_comp_sheafifyDirectSumIso_inv N i),
    sheafification_map_comp_sheafifyHomOfPresheafHom,
    inclHom_directSumDesc, sheafifyHomOfPresheafHom_val]
  exact ((sheafificationDirectSumComponentIso N).app ⟨i⟩).inv_hom_id_assoc (φ i)

end SheafifiedDirectSum

end Stacks

namespace Stacks.AlgebraicGeometry.ProjConeTwist

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison
open Stacks.AlgebraicGeometry.ProjAndSpec (puncturedConeFunction puncturedConeSmul
  puncturedConeProj)

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {f : A}

/-- Localized multiplication by `a` is multiplication by the fraction `a / 1`. -/
private theorem localizedModule_map_mulLeft {P : Submonoid A} (a : A) (z : Localization P) :
    LocalizedModule.map P (LinearMap.mulLeft A a) z = Localization.mk a 1 * z := by
  induction z using Localization.induction_on with
  | H y =>
    change LocalizedModule.map P (LinearMap.mulLeft A a) (LocalizedModule.mk y.1 y.2) = _
    rw [LocalizedModule.map_mk, Localization.mk_mul]
    simp only [LinearMap.mulLeft_apply, one_mul]
    rfl

/-- The comparison map `(B[1/σ f · ψ f])₀ → A[1/f]` sends the degree-zero fraction `σ a / 1` to
`a / 1`. -/
theorem puncturedToLocalization_fromZeroRingHom_sigma (a : A) :
    puncturedToLocalization 𝒜 (f := f) (HomogeneousLocalization.fromZeroRingHom (grading 𝒜)
      (Submonoid.powers (sigmaMulPsi 𝒜 f)) (sigma 𝒜 a)) = Localization.mk a 1 := by
  rw [puncturedToLocalization, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change Localization.awayLift _ _ _
      (Localization.mk ((sigma 𝒜 a : grading 𝒜 0) : TruncationRing 𝒜) 1) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq, RingHom.comp_apply,
    forgetDegree_coe_sigma, Localization.mk_one_eq_algebraMap]

/-- **The punctured degreewise inclusion carries multiplication by a homogeneous `a ∈ A_k` to
multiplication by `σ a / 1`**, over a standard open `D₊(f)`. -/
theorem puncturedConeTwistAwayHom_twistMulLeftInt (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℕ}
    (a : A) (ha : a ∈ 𝒜 k) (m : ℤ)
    (y : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    puncturedConeTwistAwayHom 𝒜 ((k : ℤ) + m) d hf hd
        ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y) =
      HomogeneousLocalization.fromZeroRingHom (grading 𝒜) (Submonoid.powers (sigmaMulPsi 𝒜 f))
          (sigma 𝒜 a) * puncturedConeTwistAwayHom 𝒜 m d hf hd y := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  have h1 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd
    ((k : ℤ) + m) ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)
  have h2 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd m y
  have h3 := twistMulLeftInt_standardOpen 𝒜 ⟨a, ha⟩ m hf hd y
  rw [map_mul, puncturedToLocalization_fromZeroRingHom_sigma]
  exact h1.trans (h3.trans ((localizedModule_map_mulLeft a _).trans (congrArg _ h2.symm)))

/-- **On the part of the punctured cone over `D₊(f)`, the function of `a ∈ A`** is the image of
the degree-zero fraction `σ a / 1` of `(B[1/σ f · ψ f])₀`, as ring maps out of `A`. -/
theorem puncturedConeFunction_restrict (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((openUInL 𝒜).ι ≫ toSpecA 𝒜).appTop ≫
        (openUInL 𝒜).toScheme.presheaf.map
          (homOfLE (le_top : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ
            AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op =
      CommRingCat.ofHom (sigma 𝒜).toRingHom ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (grading 𝒜)
          (Submonoid.powers (sigmaMulPsi 𝒜 f))) ≫
        AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 f) ≫
        puncturedChartRestrict 𝒜 d hf hd := by
  have hg : sigmaMulPsi 𝒜 f ∈ grading 𝒜 d := sigmaMulPsi_mem_grading 𝒜 d hf
  have e1 := Scheme.Hom.appLE_comp_appLE (openUInL 𝒜).ι (toSpecA 𝒜) ⊤
    (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
    (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.le_preimage_top _ _)
    (puncturedPi_preimage_basicOpen 𝒜 d hf hd).le
  have e2 := Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Proj.toSpecZero (grading 𝒜))
    (Spec.map (CommRingCat.ofHom (sigma 𝒜).toRingHom)) ⊤ ⊤
    (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f)) (by simp)
    (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.le_preimage_top _ _)
  have e3 : (Spec.map (CommRingCat.ofHom (sigma 𝒜).toRingHom)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (sigma 𝒜).toRingHom)).appTop :=
    Scheme.Hom.appLE_eq_app _
  have e4 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (sigma 𝒜).toRingHom)
  have e5 := Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toSpecZero_appLE
    (grading 𝒜) hg hd
  have e2' : (toSpecA 𝒜).appLE ⊤ (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
      (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.le_preimage_top _ _) =
      (Spec.map (CommRingCat.ofHom (sigma 𝒜).toRingHom)).appLE ⊤ ⊤ (by simp) ≫
        (AlgebraicGeometry.Proj.toSpecZero (grading 𝒜)).appLE ⊤
          (AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (sigmaMulPsi 𝒜 f))
          (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.le_preimage_top _ _) :=
    e2.symm
  have e0 : ((openUInL 𝒜).ι ≫ toSpecA 𝒜).appTop ≫
      (openUInL 𝒜).toScheme.presheaf.map
        (homOfLE (le_top : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⊤)).op =
      ((openUInL 𝒜).ι ≫ toSpecA 𝒜).appLE ⊤
        (((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.le_preimage_top _ _) := rfl
  rw [e0, ← e1, e2', e3]
  simp only [Category.assoc]
  rw [← reassoc_of% e4, reassoc_of% e5]
  rfl

/-- **Over a standard open, the punctured degreewise inclusion carries multiplication by a
homogeneous `a ∈ A_k` to multiplication by the function of `a`.** -/
theorem puncturedTwistHom_twistMulLeftInt_positiveBasicOpen (p : PositiveElem 𝒜) {k : ℕ}
    (a : A) (ha : a ∈ 𝒜 k) (m : ℤ)
    (y : (twistingSheaf 𝒜 m).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
        (puncturedTwistHom 𝒜 ((k : ℤ) + m)).val.app (op (positiveBasicOpen 𝒜 p))
          ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)) =
      (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
          (openUInL 𝒜).toScheme.presheaf.map (homOfLE le_top).op
            (puncturedConeFunction (truncationConeData 𝒜) a)) *
        (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
          (puncturedTwistHom 𝒜 m).val.app (op (positiveBasicOpen 𝒜 p)) y) := by
  have hA := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 ((k : ℤ) + m) p)
    ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)
  have hB := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 m p) y
  have hC := puncturedConeTwistApp_apply 𝒜 ((k : ℤ) + m) (Classical.choose p.2)
    (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1
    ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)
  have hD := puncturedConeTwistApp_apply 𝒜 m (Classical.choose p.2)
    (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1 y
  have hE := puncturedConeTwistAwayHom_twistMulLeftInt 𝒜 (Classical.choose p.2)
    (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1 a ha m y
  have hF := ConcreteCategory.congr_hom (puncturedConeFunction_restrict 𝒜 (Classical.choose p.2)
    (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1) a
  simp only [CategoryTheory.comp_apply] at hF
  have hM : ∀ X Z : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 p.1),
      (puncturedChartRestrict 𝒜 (Classical.choose p.2) (Classical.choose_spec p.2).2
          (Classical.choose_spec p.2).1).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 p.1)).hom (X * Z)) =
      (puncturedChartRestrict 𝒜 (Classical.choose p.2) (Classical.choose_spec p.2).2
          (Classical.choose_spec p.2).1).hom
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 p.1)).hom X) *
        (puncturedChartRestrict 𝒜 (Classical.choose p.2) (Classical.choose_spec p.2).2
          (Classical.choose_spec p.2).1).hom
          ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 p.1)).hom Z) := by
    intro X Z
    rw [map_mul, map_mul]
  exact hA.trans (hC.trans ((congrArg (fun z =>
      (puncturedChartRestrict 𝒜 (Classical.choose p.2) (Classical.choose_spec p.2).2
          (Classical.choose_spec p.2).1).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (sigmaMulPsi 𝒜 p.1)).hom z)) hE).trans
    ((hM _ _).trans (congrArg₂ (· * ·) hF.symm (hD.symm.trans hB.symm)))))

/-- **The punctured degreewise inclusion carries multiplication by a homogeneous `a ∈ A_k` to
multiplication by the function of `a`**, over every open of `P`. -/
theorem puncturedTwistHom_twistMulLeftInt_app {k : ℕ} (a : A) (ha : a ∈ 𝒜 k) (m : ℤ)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (y : (twistingSheaf 𝒜 m).val.obj (op V)) :
    (show puncturedConeSections 𝒜 V from
        (puncturedTwistHom 𝒜 ((k : ℤ) + m)).val.app (op V)
          ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)) =
      (show puncturedConeSections 𝒜 V from
          (openUInL 𝒜).toScheme.presheaf.map (homOfLE le_top).op
            (puncturedConeFunction (truncationConeData 𝒜) a)) *
        (show puncturedConeSections 𝒜 V from (puncturedTwistHom 𝒜 m).val.app (op V) y) := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)) (positiveBasicOpen 𝒜)
    (isBasis_positiveBasicOpen 𝒜) _ _ fun p hle => ?_
  have h1 := PresheafOfModules.naturality_apply (puncturedTwistHom 𝒜 ((k : ℤ) + m)).val
    (homOfLE hle).op ((twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val.app _ y)
  have h2 := PresheafOfModules.naturality_apply (twistMulLeftInt 𝒜 ⟨a, ha⟩ m).val
    (homOfLE hle).op y
  have h3 := PresheafOfModules.naturality_apply (puncturedTwistHom 𝒜 m).val (homOfLE hle).op y
  have h4 := puncturedPushforwardStructureSheaf_map_mul 𝒜 hle
    ((openUInL 𝒜).toScheme.presheaf.map (homOfLE le_top).op
      (puncturedConeFunction (truncationConeData 𝒜) a))
    ((puncturedTwistHom 𝒜 m).val.app (op V) y)
  have h5 := ConcreteCategory.congr_hom ((openUInL 𝒜).toScheme.presheaf.map_comp
    (homOfLE (le_top : ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ V ≤ ⊤)).op
    ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE hle)).op).symm
    (puncturedConeFunction (truncationConeData 𝒜) a)
  have h6 := puncturedTwistHom_twistMulLeftInt_positiveBasicOpen 𝒜 p a ha m
    ((twistingSheaf 𝒜 m).val.map (homOfLE hle).op y)
  exact h1.symm.trans ((congrArg _ h2).trans (h6.trans
    ((congrArg₂ (fun x y : puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) => x * y) h5 h3).trans
      h4.symm)))

/-- **The punctured degreewise inclusion carries multiplication by a homogeneous `a ∈ A_k` to
multiplication by the function of `a`**, as morphisms of sheaves of `𝒪_P`-modules
`𝒪_P(m) ⟶ (π|_U)_*𝒪_U`. -/
theorem puncturedTwistHom_comp_smul {k : ℕ} (a : A) (ha : a ∈ 𝒜 k) (m : ℤ) :
    puncturedTwistHom 𝒜 m ≫ (Scheme.Modules.pushforward
        (puncturedConeProj (truncationConeData 𝒜))).map
        ((puncturedConeSmul (truncationConeData 𝒜) a).asHom.app
          (SheafOfModules.unit (openUInL 𝒜).toScheme.ringCatSheaf)) =
      twistMulLeftInt 𝒜 ⟨a, ha⟩ m ≫ puncturedTwistHom 𝒜 ((k : ℤ) + m) := by
  ext V y
  exact (puncturedTwistHom_twistMulLeftInt_app 𝒜 a ha m V.unop y).symm

/-- On the `m`-th summand, the inverse of `(π|_U)_*𝒪_U ≅ ⨁_m 𝒪_P(m)` is the punctured degreewise
inclusion of `𝒪_P(m)`. -/
theorem ι_puncturedConeStructureCoproductIso_inv (m : ℤ) :
    Sigma.ι (fun m : ℤ => twistingSheaf 𝒜 m) m ≫ (puncturedConeStructureCoproductIso 𝒜).inv =
      puncturedTwistHom 𝒜 m := by
  have h : (puncturedConeStructureCoproductIso 𝒜).inv =
      (Stacks.sheafifyDirectSumIso fun m : ℤ => twistingSheaf 𝒜 m).inv ≫
        Stacks.sheafifyHomOfPresheafHom (puncturedTwistDirectSumHom 𝒜) := rfl
  have h' : puncturedTwistDirectSumHom 𝒜 =
      Stacks.directSumDesc (fun m : ℤ => (twistingSheaf 𝒜 m).val)
        fun m => (puncturedTwistHom 𝒜 m).val := rfl
  rw [h, h']
  exact Stacks.ι_sheafifyDirectSumIso_inv_comp_sheafifyHomOfPresheafHom
    (fun m : ℤ => twistingSheaf 𝒜 m) (fun m => puncturedTwistHom 𝒜 m) m

/-- `ι_puncturedConeStructureCoproductIso_inv`, for the identification
`puncturedConeStructurePushforwardCoproductIso` in the form the decomposition consumes. -/
theorem ι_puncturedConeStructurePushforwardCoproductIso_inv (m : ℤ) :
    Sigma.ι (fun m : ℤ => twistingSheaf 𝒜 m) m ≫
        (puncturedConeStructurePushforwardCoproductIso 𝒜).inv =
      puncturedTwistHom 𝒜 m := by
  -- The two sources of the identification agree only up to unfolding, which the kernel does
  -- slowly inside a composite; transport along an equation of objects instead.
  have key : ∀ (Y : (AlgebraicGeometry.Proj 𝒜).Modules)
      (hY : Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜) = Y),
      Sigma.ι (fun m : ℤ => twistingSheaf 𝒜 m) m ≫
          (Eq.rec (motive := fun Y _ => Y ≅ ∐ fun m : ℤ => twistingSheaf 𝒜 m)
            (puncturedConeStructureCoproductIso 𝒜) hY).inv =
        Eq.rec (motive := fun Y _ => twistingSheaf 𝒜 m ⟶ Y) (puncturedTwistHom 𝒜 m) hY := by
    rintro _ rfl
    exact ι_puncturedConeStructureCoproductIso_inv 𝒜 m
  exact key ((Scheme.Modules.pushforward (puncturedConeProj (truncationConeData 𝒜))).obj
    (SheafOfModules.unit
      (Stacks.AlgebraicGeometry.ProjAndSpec.openUInL (truncationConeData 𝒜)).toScheme.ringCatSheaf))
    rfl

end Stacks.AlgebraicGeometry.ProjConeTwist

namespace Stacks.AlgebraicGeometry.ProjAndSpec

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation
open Stacks.Duality (derivedPushforward)

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- **The `A`-module structures on the two sides of `RΓ(U, 𝓕_U) = ⨁_m RΓ(P, 𝓕(m))` agree.** On
the left `A` acts through `U ⊆ X = Spec A`, by `puncturedConeSmul`; on the right a homogeneous
`a ∈ A_k` acts by sending the summand `RΓ(P, 𝓕(m))` to `RΓ(P, 𝓕(k + m))` through multiplication
`𝓕(m) ⟶ 𝓕(k + m)` by the section `a` of `𝒪_P(k)`. The decomposition
`derivedPushforwardPuncturedConeIsoTruncation` intertwines the two, for every homogeneous `a`.
`derivedPushforwardPuncturedConeIsoTruncation_hom_smul_all` extends this to every `a ∈ A`. -/
theorem derivedPushforwardPuncturedConeIsoTruncation_hom_smul
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent] {k : ℕ} (a : A) (ha : a ∈ 𝒜 k) :
    (derivedPushforward (puncturedConeProj (truncationConeData 𝒜) ≫
          AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
        ((DerivedCategory.singleFunctor (openUInL (truncationConeData 𝒜)).toScheme.Modules 0).map
          ((puncturedConeSmul (truncationConeData 𝒜) a).asHom.app
            (puncturedConePullback (truncationConeData 𝒜) F) :
            puncturedConePullback (truncationConeData 𝒜) F ⟶
              puncturedConePullback (truncationConeData 𝒜) F)) ≫
        (derivedPushforwardPuncturedConeIsoTruncation 𝒜 F).hom =
      (derivedPushforwardPuncturedConeIsoTruncation 𝒜 F).hom ≫
        Sigma.map' (fun m : ℤ => (k : ℤ) + m) (fun m =>
          (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
            ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).obj F).map
                (twistMulLeftInt 𝒜 ⟨a, ha⟩ m)))) :=
  derivedPushforwardPuncturedConeIsoOfStructureIso_hom_smul (truncationConeData 𝒜) F
    (Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso 𝒜) a
    (fun m : ℤ => (k : ℤ) + m) (fun m => twistMulLeftInt 𝒜 ⟨a, ha⟩ m)
    (fun m => Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom 𝒜 m)
    (Stacks.AlgebraicGeometry.ProjConeTwist.ι_puncturedConeStructurePushforwardCoproductIso_inv 𝒜)
    fun m => by
      ext V y
      exact (Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_twistMulLeftInt_app 𝒜 a ha m
        V.unop y).symm

open Classical in
/-- **The graded `A`-module structure on `⨁_m RΓ(P, 𝓕(m))`.** An element `a ∈ A` acts as the sum,
over the degrees `k` of its homogeneous components `a_k`, of the morphisms sending the summand
`RΓ(P, 𝓕(m))` to `RΓ(P, 𝓕(k + m))` by multiplication `𝓕(m) ⟶ 𝓕(k + m)` by `a_k`. -/
def twistSumSmul (F : (AlgebraicGeometry.Proj 𝒜).Modules) (a : A) :
    (∐ fun m : ℤ => (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistSheafOfModules 𝒜 F m))) ⟶
      ∐ fun m : ℤ => (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistSheafOfModules 𝒜 F m)) :=
  ∑ k ∈ (DirectSum.decompose 𝒜 a).support,
    Sigma.map' (fun m : ℤ => (k : ℤ) + m) (fun m =>
      (derivedPushforward (AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
        ((DerivedCategory.singleFunctor (AlgebraicGeometry.Proj 𝒜).Modules 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).obj F).map
            (twistMulLeftInt 𝒜
              ⟨(DirectSum.decompose 𝒜 a k : A), (DirectSum.decompose 𝒜 a k).2⟩ m))))

open Classical in
/-- **The `A`-module structures on the two sides of `RΓ(U, 𝓕_U) = ⨁_m RΓ(P, 𝓕(m))` agree.** For
every `a ∈ A`, the decomposition `derivedPushforwardPuncturedConeIsoTruncation` carries
multiplication by `a` on `RΓ(U, 𝓕_U)`, through `U ⊆ X = Spec A` (`puncturedConeSmul`), to the
graded action `twistSumSmul` of `a` on `⨁_m RΓ(P, 𝓕(m))`, in which each homogeneous component
`a_k` sends `RΓ(P, 𝓕(m))` to `RΓ(P, 𝓕(k + m))`. -/
@[stacks 0EKH "the A-module structure on the right of RΓ(U, F_U) = ⊕_m RΓ(P, F ⊗ O_P(m)), where \
a ∈ A acts through its homogeneous components a_k : F(m) → F(k + m), agrees with the one on the \
left coming from U ⊆ X; RΓ is read as derived direct image to Spec A₀"]
theorem derivedPushforwardPuncturedConeIsoTruncation_hom_smul_all
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    [F.IsQuasicoherent] (a : A) :
    (derivedPushforward (puncturedConeProj (truncationConeData 𝒜) ≫
          AlgebraicGeometry.Proj.toSpecZero 𝒜)).map
        ((DerivedCategory.singleFunctor (openUInL (truncationConeData 𝒜)).toScheme.Modules 0).map
          ((puncturedConeSmul (truncationConeData 𝒜) a).asHom.app
            (puncturedConePullback (truncationConeData 𝒜) F) :
            puncturedConePullback (truncationConeData 𝒜) F ⟶
              puncturedConePullback (truncationConeData 𝒜) F)) ≫
        (derivedPushforwardPuncturedConeIsoTruncation 𝒜 F).hom =
      (derivedPushforwardPuncturedConeIsoTruncation 𝒜 F).hom ≫ twistSumSmul 𝒜 F a := by
  have hL : (puncturedConeSmul (truncationConeData 𝒜) a) =
      ∑ k ∈ (DirectSum.decompose 𝒜 a).support,
        puncturedConeSmul (truncationConeData 𝒜) (DirectSum.decompose 𝒜 a k : A) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact map_sum (puncturedConeSmulAddHom (truncationConeData 𝒜)) _ _
  rw [hL, End.sum_asHom, NatTrans.app_sum, Functor.map_sum, Functor.map_sum, Preadditive.sum_comp,
    twistSumSmul, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun k _ =>
    derivedPushforwardPuncturedConeIsoTruncation_hom_smul 𝒜 F
      (DirectSum.decompose 𝒜 a k : A) (DirectSum.decompose 𝒜 a k).2

end Stacks.AlgebraicGeometry.ProjAndSpec
