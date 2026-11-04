module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitIdealMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSectionSets
public import StacksFrontier.Deformation.AlgebraExtension.InverseLimitComponents
public import StacksFrontier.Deformation.AlgebraExtension.KernelGlobalSectionSets

/-!
# The map `φ` of the tower problem on global sections, on underlying sheaves of sets

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] compares `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ`
(`AlgebraicGeometry.ProperFlatFibre.towerLimitKernelMap`) with the canonical map of
[Stacks Project, Tag 0D3F] on the sections `1 ⊗ m`. This file computes the `n`-th component of
`φ` on the pullback `f^*σ` of a global section `σ` of `𝒞_{Y₀/Y}`, read in the middle term
`𝒪_{Xₙ}` of the `n`-th extension: it is the inverse image along `f` of the section `σ` read in
`i⁻¹𝒪_Y`, carried to `𝒜 = lim 𝒪_{Xₙ}` and projected to `𝒪_{Xₙ}`.

## Main results

* In `Deformation.ToposThickening.RingedToposExtensionProblem`,
  `ringOneHom_comp_map_comp_π_comp_inclSheafSets_of_kernelInclusion`: the same computation for
  an abstract inverse limit of algebra extensions and an abstract map `f⁻¹𝒪' ⟶ lim Fₙ` carrying
  the inverse image of the base ideal to the kernel through `φ ∘ c`.
* `AlgebraicGeometry.ProperFlatFibre.ringOneHom_comp_map_towerLimitKernelMap_π_comp_inclSheafSets`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u v w v' u' w'

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Deformation.ToposThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

section InverseImage

variable {X : RingedTopos.{v, u, w}} {D : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [D.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X D) {A : Sheaf D.J CommRingCat.{w'}} {a : A ⟶ D.O}
  {M : SheafOfModules.{w'} ((sheafCompose D.J (forget₂ CommRingCat.{w'} RingCat.{w'})).obj D.O)}
  (E : AlgebraExtension a M)

/-- **The base ideal of `ofBaseAlgebraExtension` on the inverse image of a global section**: for
a problem equal to the one attached to an algebra extension `0 → ℳ → 𝒪' → 𝒪_D → 0` of the base,
the inverse image along `f` of a global section `t` of `ℳ`, read in the base ideal `f⁻¹ℳ` and
followed by its inclusion into `f⁻¹𝒪'`, is the inverse image of `t` read in `𝒪'`. The section is
passed as any `τ` heterogeneously equal to the inverse image of `t`, so that the statement applies
to a problem whose base ideal is only definitionally `f⁻¹ℳ`. -/
theorem comp_map_idealInclusion_of_eq_ofBaseAlgebraExtension (Sp : RingedToposExtensionProblem X D)
    (G : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O))
    (c : inverseImageExtensionIdeal f (M := M) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f.fSharpInverseImage)).obj G)
    (hSp : Sp = RingedToposExtensionProblem.ofBaseAlgebraExtension f E G c)
    (t : ⊤_ (Sheaf D.J (Type w')) ⟶ (moduleSheafFunctor
      ((sheafCompose D.J (forget₂ CommRingCat.{w'} RingCat.{w'})).obj D.O)).obj M)
    (τ : ⊤_ (Sheaf X.J (Type w)) ⟶ (moduleSheafFunctor
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor Sp.f.toToposHom).obj D.O))).obj Sp.I)
    (hτ : HEq τ (f.toToposHom.inverseImage.globalSectionMap t)) :
    HEq (τ ≫ (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor Sp.f.toToposHom).obj Sp.baseExtension))).map
          Sp.idealInclusion)
      (f.toToposHom.inverseImage.globalSectionMap (t ≫ E.inclSheafSets)) := by
  subst hSp
  obtain rfl := eq_of_heq hτ
  exact heq_of_eq (hom_ext_sections fun U p => (inverseImageExtensionIdealIncl_val_app f E U
      _).trans
    (sectionsFunctor_map_congr (Functor.globalSectionMap_comp f.toToposHom.inverseImage t
      E.inclSheafSets) U p))

end InverseImage

namespace RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {D : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [D.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (Sp : RingedToposExtensionProblem X D)

/-- **A map to an inverse limit of algebra extensions carrying the base ideal to the kernel, read
on a global section of `𝒢`.** Let `0 → ℳₙ → 𝒪'ₙ → 𝒪_X → 0` be algebra extensions with
`Fₙ ≅ 𝒪'ₙ`, and let `φ : 𝒢 ⟶ lim ℳₙ` and `b : f⁻¹𝒪'_D ⟶ lim Fₙ` be such that `b` carries the
image of a section `x` of the base ideal to the image of `φ(c(x))`. If a global section `w` of
`𝒢` is, on sets, `c` applied to a global section `τ` of the base ideal, then the unit section
followed by `w`, `φ`, the `n`-th projection and `ℳₙ ⊆ 𝒪'ₙ` is `τ` read in `f⁻¹𝒪'_D`, followed by
`b`, the `n`-th projection and `Fₙ ≅ 𝒪'ₙ`. -/
theorem ringOneHom_comp_map_comp_π_comp_inclSheafSets_of_kernelInclusion
    (F : ℕᵒᵖ ⥤ Sheaf X.J CommRingCat.{w}) [HasLimit F] (ρ : F ⟶ (Functor.const _).obj X.O)
    {A' : ℕ → Sheaf X.J CommRingCat.{w}} {a' : ∀ n, A' n ⟶ X.O}
    {M' : ℕ → SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (P : ∀ n, AlgebraExtension (a' n) (M' n)) (e : ∀ n, F.obj (op n) ≅ (P n).extension)
    (he : ∀ n, (e n).hom ≫ (P n).reduction = ρ.app (op n))
    {hN : HasLimit (AlgebraExtension.InverseLimit.idealSystem F ρ P e he)}
    (φ : Sp.G ⟶ limit (AlgebraExtension.InverseLimit.idealSystem F ρ P e he))
    (b : (inverseImageCommRingFunctor Sp.f.toToposHom).obj Sp.baseExtension ⟶ limit F)
    (hb : ∀ (U : X.Cᵒᵖ) (x : Sp.I.val.obj U),
      b.hom.app U (Sp.idealInclusion.val.app U x) =
        (AlgebraExtension.InverseLimit.kernelInclusion F ρ P e he).val.app U
          (φ.val.app U (Sp.c.val.app U x)))
    (w : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ⟶
      Sp.G)
    (τ : ⊤_ (Sheaf X.J (Type w)) ⟶ (moduleSheafFunctor
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor Sp.f.toToposHom).obj D.O))).obj Sp.I)
    (hw : ringOneHom ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ≫
        (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          X.O)).map w =
      τ ≫ (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor Sp.f.toToposHom).obj D.O))).map Sp.c)
    (n : ℕ) :
    ringOneHom ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ≫
        (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          X.O)).map
          (w ≫ φ ≫ limit.π (AlgebraExtension.InverseLimit.idealSystem F ρ P e he) (op n)) ≫
        (P n).inclSheafSets =
      (τ ≫ (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor Sp.f.toToposHom).obj Sp.baseExtension))).map
          Sp.idealInclusion) ≫
        (sheafCompose X.J (forget RingCat.{w})).map
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (b ≫ limit.π F (op n) ≫ (e n).hom)) := by
  refine hom_ext_sections fun U p => ?_
  have h1 := sectionsFunctor_map_congr hw U p
  refine (AlgebraExtension.InverseLimit.incl_idealComponent F ρ P e he U n
    (φ.val.app U ((sectionsFunctor _ U).map
      (ringOneHom ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ≫
        (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          X.O)).map w) p))).trans ?_
  refine congrArg (fun y => (e n).hom.hom.app U ((limit.π F (op n)).hom.app U y)) ?_
  refine (congrArg (fun y => (AlgebraExtension.InverseLimit.kernelInclusion F ρ P e he).val.app U
    (φ.val.app U y)) h1).trans ?_
  exact (hb U _).symm

/-- **A map to an inverse limit of algebra extensions carrying the base ideal to the kernel, on a
global section, from its reading in the middle terms.** In the situation of
`ringOneHom_comp_map_comp_π_comp_inclSheafSets_of_kernelInclusion`, if `τ` read in `f⁻¹𝒪'_D`,
followed by `b`, the `n`-th projection and `Fₙ ≅ 𝒪'ₙ`, is the image in `𝒪'ₙ` of a global
section `w'` of `ℳₙ`, then `w` followed by `φ` and the `n`-th projection is `w'`: global
sections of the kernel are determined by their images in the middle term. -/
theorem comp_comp_π_eq_of_kernelInclusion
    (F : ℕᵒᵖ ⥤ Sheaf X.J CommRingCat.{w}) [HasLimit F] (ρ : F ⟶ (Functor.const _).obj X.O)
    {A' : ℕ → Sheaf X.J CommRingCat.{w}} {a' : ∀ n, A' n ⟶ X.O}
    {M' : ℕ → SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (P : ∀ n, AlgebraExtension (a' n) (M' n)) (e : ∀ n, F.obj (op n) ≅ (P n).extension)
    (he : ∀ n, (e n).hom ≫ (P n).reduction = ρ.app (op n))
    {hN : HasLimit (AlgebraExtension.InverseLimit.idealSystem F ρ P e he)}
    (φ : Sp.G ⟶ limit (AlgebraExtension.InverseLimit.idealSystem F ρ P e he))
    (b : (inverseImageCommRingFunctor Sp.f.toToposHom).obj Sp.baseExtension ⟶ limit F)
    (hb : ∀ (U : X.Cᵒᵖ) (x : Sp.I.val.obj U),
      b.hom.app U (Sp.idealInclusion.val.app U x) =
        (AlgebraExtension.InverseLimit.kernelInclusion F ρ P e he).val.app U
          (φ.val.app U (Sp.c.val.app U x)))
    (w : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ⟶
      Sp.G)
    (τ : ⊤_ (Sheaf X.J (Type w)) ⟶ (moduleSheafFunctor
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor Sp.f.toToposHom).obj D.O))).obj Sp.I)
    (hw : ringOneHom ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ≫
        (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          X.O)).map w =
      τ ≫ (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor Sp.f.toToposHom).obj D.O))).map Sp.c)
    (n : ℕ)
    (w' : SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ⟶
      (AlgebraExtension.InverseLimit.idealSystem F ρ P e he).obj (op n))
    (hτ : (τ ≫ (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor Sp.f.toToposHom).obj Sp.baseExtension))).map
          Sp.idealInclusion) ≫
        (sheafCompose X.J (forget RingCat.{w})).map
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (b ≫ limit.π F (op n) ≫ (e n).hom)) =
      ringOneHom ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O) ≫
        (moduleSheafFunctor ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          X.O)).map w' ≫ (P n).inclSheafSets) :
    w ≫ φ ≫ limit.π (AlgebraExtension.InverseLimit.idealSystem F ρ P e he) (op n) = w' :=
  AlgebraExtension.eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq (P n)
    ((Sp.ringOneHom_comp_map_comp_π_comp_inclSheafSets_of_kernelInclusion F ρ P e he φ b hb w τ hw
      n).trans hτ)

end RingedToposExtensionProblem

end Deformation.ToposThickening

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- **The pullback `f^*σ` of a global section of `𝒞_{Y₀/Y}`, on sheaves of sets**, is the map
`c : f⁻¹𝒞_{Y₀/Y} ⟶ f^*𝒞_{Y₀/Y}` of the tower problem applied to the inverse image of `σ`. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_eq_towerProblem_c
    (σ : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace
        (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos
        B S hS (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit
        hc) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
        ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace
        ξ 0)).O)).map
        (Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ) =
      (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap (ringOneHom ((sheafCompose
          (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
          CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
          (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S
          hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O)).map σ) ≫
          (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)).toToposHom).obj
          (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O))).map (towerProblem
          ξ hsurj hsq e cR hcR c eLimit hc).c :=
  Space.ringOneHom_comp_map_modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ

/-- The extension problem of the body of [Stacks Project, Tag 0D3X] is the problem attached to the
base thickening `0 → 𝒞_{Y₀/Y} → i⁻¹𝒪_Y → 𝒪_{Y₀} → 0`. -/
theorem towerProblem_eq_ofBaseAlgebraExtension :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc) =
      Deformation.ToposThickening.RingedToposExtensionProblem.ofBaseAlgebraExtension
        (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)) (limitBaseExtension ξ hsurj
            hsq e cR hcR c eLimit hc) (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G
            (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).c :=
  rfl

/-- **The base ideal of the tower problem on the inverse image of a global section of
`𝒞_{Y₀/Y}`**: read in `f⁻¹i⁻¹𝒪_Y`, it is the inverse image of the section read in `i⁻¹𝒪_Y`. -/
theorem globalSectionMap_comp_map_towerProblem_idealInclusion (σ : SheafOfModules.unit
    ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
    CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ
    0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc) :
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
        0)).toToposHom.inverseImage.globalSectionMap (ringOneHom ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace
        (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos
        B S hS (schemeSpace (towerBase ξ 0))).O)).map σ) ≫ (moduleSheafFunctor ((sheafCompose
        (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)).toToposHom).obj
        (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit hc).extension))).map (towerProblem ξ
        hsurj hsq e cR hcR c eLimit hc).idealInclusion =
      (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
        ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
            0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
            (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
            (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
            CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
            (towerBase ξ 0))).O)).map σ) ≫ (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit
            hc).inclSheafSets) :=
  eq_of_heq (Deformation.ToposThickening.comp_map_idealInclusion_of_eq_ofBaseAlgebraExtension
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)) (limitBaseExtension ξ hsurj hsq
        e cR hcR c eLimit hc) (towerProblem ξ hsurj hsq e cR hcR c eLimit hc) (towerProblem ξ hsurj
        hsq e cR hcR c eLimit hc).G (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).c
    (towerProblem_eq_ofBaseAlgebraExtension ξ hsurj hsq e cR hcR c eLimit hc) _ _ HEq.rfl)

/-- **The `n`-th component of `φ` on the pullback of a global section, read in `𝒪_{Xₙ}`**, as the
inverse image of the section read in the base ideal of the tower problem. -/
theorem ringOneHom_comp_map_towerLimitKernelMap_π_comp_inclSheafSets_eq_idealInclusion (n : ℕ)
    (σ : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace
        (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos
        B S hS (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit
        hc) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
        ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace
        ξ 0)).O)).map
          (Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ ≫
            towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
            limit.π (towerIdealSystem ξ hsurj hsq e he) (op n)) ≫
        (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets =
      ((Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap (ringOneHom ((sheafCompose
          (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
          CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
          (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S
          hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O)).map σ) ≫
          (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)).toToposHom).obj
          (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit hc).extension))).map (towerProblem ξ
          hsurj hsq e cR hcR c eLimit hc).idealInclusion) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
            RingCat.{u})).map
          ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
              CommRingCat.{u} RingCat.{u})).map
            (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫
              limit.π (towerRingSystem ξ) (op n) ≫
              (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom)) :=
  open Deformation.ToposThickening in
  RingedToposExtensionProblem.ringOneHom_comp_map_comp_π_comp_inclSheafSets_of_kernelInclusion
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc) (towerRingSystem ξ) (towerRingReduction ξ)
    (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _))
    (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)
    (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc)
    (towerLimitKernelMap_ideal ξ hsurj hsq e he cR hcR c eLimit hc)
    (Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ) _
    (ringOneHom_comp_map_modulePullbackGlobalSection_eq_towerProblem_c ξ hsurj hsq e cR hcR c
      eLimit hc σ) n

/-- **The `n`-th component of `φ` on the pullback of a global section, read in `𝒪_{Xₙ}`**: for a
global section `σ` of `𝒞_{Y₀/Y}`, the unit section followed by `f^*σ`, `φ`, the `n`-th
projection and the inclusion into the middle term of the `n`-th extension is the inverse image
along `f` of the global section `σ` read in `i⁻¹𝒪_Y`, carried to `𝒜 = lim 𝒪_{Xₙ}` and projected
to `𝒪_{Xₙ}`. -/
theorem ringOneHom_comp_map_towerLimitKernelMap_π_comp_inclSheafSets (n : ℕ) (σ :
    SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
    0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
    (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
        ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace
        ξ 0)).O)).map
          (Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ ≫
            towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
            limit.π (towerIdealSystem ξ hsurj hsq e he) (op n)) ≫
        (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets =
      (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
          ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
              0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
              (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
              (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
              CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
              (towerBase ξ 0))).O)).map σ) ≫ (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit
              hc).inclSheafSets) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
            RingCat.{u})).map
          ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
              CommRingCat.{u} RingCat.{u})).map
            (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫
              limit.π (towerRingSystem ξ) (op n) ≫
              (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom)) :=
  (ringOneHom_comp_map_towerLimitKernelMap_π_comp_inclSheafSets_eq_idealInclusion ξ hsurj hsq e he
    cR hcR c eLimit hc n σ).trans
    (congrArg (· ≫ _) (globalSectionMap_comp_map_towerProblem_idealInclusion ξ hsurj hsq e cR hcR
      c eLimit hc σ))

/-- **The `n`-th component of `φ` on the pullback of a global section, from its reading in
`𝒪_{Xₙ}`.** For a global section `σ` of `𝒞_{Y₀/Y}` and a global section `w'` of `𝒪_{X₀} ⊗ Iₙ`, if
the inverse image along `f` of `σ` read in `i⁻¹𝒪_Y`, carried to `𝒜 = lim 𝒪_{Xₙ}` and projected to
`𝒪_{Xₙ}`, is the image of `w'` in `𝒪_{Xₙ}`, then `f^*σ` followed by `φ` and the `n`-th projection
is `w'`. -/
theorem modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets (n : ℕ) (σ :
    SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
    0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
    (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)
    (w' : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
        (towerSpace ξ 0)).O) ⟶ (towerIdealSystem ξ hsurj hsq e he).obj (op n))
    (hτ : (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
          ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
              0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
              (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
              (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
              CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
              (towerBase ξ 0))).O)).map σ) ≫ (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit
              hc).inclSheafSets) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
            RingCat.{u})).map
          ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
              CommRingCat.{u} RingCat.{u})).map
            (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫
              limit.π (towerRingSystem ξ) (op n) ≫
              (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom)) =
      ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
        ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace
        ξ 0)).O)).map w' ≫ (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets) :
    Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) = w' :=
  Deformation.AlgebraExtension.eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq
    (towerExtension ξ hsurj hsq e he n (𝟙 _))
    ((ringOneHom_comp_map_towerLimitKernelMap_π_comp_inclSheafSets ξ hsurj hsq e he cR hcR c
      eLimit hc n σ).trans hτ)

end AlgebraicGeometry.ProperFlatFibre

end
