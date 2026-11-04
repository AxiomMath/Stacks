module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointTwists
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BasePsiComp
public import StacksFrontier.AlgebraicGeometry.TwistExistence.IsoExtOfPsi
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists at two scheme points of the base of Situation 0849, compared

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B. For a
scheme point `g : Z → X` of the base and a morphism `h : Z' ⟶ Z` of test objects, the third
assertion of Stacks 084B compares `Proj_{Z'}((g ∘ h)^*𝒜)` with `Proj_Z(g^*𝒜)`: the comparison
morphism is the identification `Proj_{Z'}((g ∘ h)^*𝒜) ≅ Proj_{Z'}(h^*(g^*𝒜))` of the two
restrictions followed by the base-change morphism of Tag 01O3. This file compares the twists of
Tag 01NR along that morphism: the inverse image of `⨁_{n ∈ ℤ} 𝒪_{Proj_Z(g^*𝒜)}(n)` is
`⨁_{n ∈ ℤ} 𝒪_{Proj_{Z'}((g ∘ h)^*𝒜)}(n)`, as sheaves of `ℤ`-graded algebras.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso`: for a graded
  algebra `A` on `Y`, `hs : Y' ⟶ Y`, an isomorphism `Φ : A₁ ≅ hs^*A` and
  `pc = relativeProjCongr Φ ≫ baseChangeHom A hs`, the isomorphism `pc^*𝒪(*) ≅ 𝒪_{Proj(A₁)}(*)`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangePsi`: the
  homogeneous-section maps of `pc^*𝒪(*)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison`: the comparison of twists
  along a morphism `pc` lying over a morphism `k : V ⟶ U` of test objects, at points `u` and
  `v = u ∘ k`. The comparison morphism of Stacks 084B (3) is the case `pc = projComparison g h`,
  `v = g ∘ h`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparisonPsi`: the homogeneous-section
  maps of the pulled-back twists.

## Main results

* `RelativeProjBaseChangeTwist.congrBaseChangePsi_comp_congrBaseChangeTwistIso` and
  `RelativeProjSituation.pointTwistComparisonPsi_comp_pointTwistComparison`: the comparison of
  twists carries `ψ` to `ψ`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso_comp` and
  `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison_comp`: the cocycle condition:
  the comparison along `pc' ≫ pc` is the comparison along `pc`, pulled back along `pc'`, followed
  by the comparison along `pc'`.
* `AlgebraicGeometry.Space.RelativeProjSituation.toScheme_map_eqToHom_projComparison`: the
  comparison morphism of Stacks 084B (3), at an equal point, is the identification of the
  restrictions followed by the base-change morphism of Tag 01O3.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

/-- The unit of `e^* ⊣ e_*`, read through `(e ≫ π₂)_* = π₁_*`, is natural. -/
theorem pushforward_unit_comp_pushforward_map_pullback_map {P₁ P₂ Y' : Scheme.{u}} (e : P₁ ⟶ P₂)
    (π₂ : P₂ ⟶ Y') (π₁ : P₁ ⟶ Y') (he : e ≫ π₂ = π₁) {X X' : P₂.Modules} (θ : X ⟶ X')
    {N : Y'.Modules} (t : (Scheme.Modules.pushforward π₁).obj
      ((Scheme.Modules.pullback e).obj X') ⟶ N) :
    (Scheme.Modules.pushforward π₂).map
        ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app X) ≫
      (Scheme.Modules.pushforwardComp e π₂).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr he).hom.app _ ≫
      (Scheme.Modules.pushforward π₁).map ((Scheme.Modules.pullback e).map θ) ≫ t =
    (Scheme.Modules.pushforward π₂).map θ ≫
      (Scheme.Modules.pushforward π₂).map
        ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app X') ≫
      (Scheme.Modules.pushforwardComp e π₂).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr he).hom.app _ ≫ t := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction e).unit.naturality θ
  have hc := (Scheme.Modules.pushforwardComp e π₂).hom.naturality
    ((Scheme.Modules.pullback e).map θ)
  have hg := (Scheme.Modules.pushforwardCongr he).hom.naturality
    ((Scheme.Modules.pullback e).map θ)
  simp only [Functor.id_map, Functor.comp_map] at hu hc
  rw [← reassoc_of% hg, ← reassoc_of% hc, ← Functor.map_comp_assoc, ← hu, Functor.map_comp_assoc]

/-- The pushforward of the degree-`k` part of the composite iso `pc^*G ≅ (e ≫ bc)^*G ≅ e^*bc^*G
≅ e^*T₂ ≅ T₁` is the composite of the pushforwards of its four components. -/
private theorem pushforward_map_congrComp_hom_app {P P₁ P₂ Y' : Scheme.{u}} (π₁ : P₁ ⟶ Y')
    (pc : P₁ ⟶ P) (e : P₁ ⟶ P₂) (bc : P₂ ⟶ P) (hpc : pc = e ≫ bc)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P.toRingedSpace))
    (T₂ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P₂.toRingedSpace))
    (T₁ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P₁.toRingedSpace))
    (θ : pbAlgS bc G ≅ T₂) (cT : pbAlgS e T₂ ≅ T₁) (k : ℤ) :
    (Scheme.Modules.pushforward π₁).map
      ((GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G hpc ≪≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G e bc).symm ≪≫
        Stacks.RingedSpace.pullbackGradedAlgebraMapIso _ θ ≪≫ cT).hom.app k) =
      (Scheme.Modules.pushforward π₁).map ((Scheme.Modules.pullbackCongr hpc).hom.app (G.piece k)) ≫
        (Scheme.Modules.pushforward π₁).map
          ((Scheme.Modules.pullbackComp e bc).inv.app (G.piece k)) ≫
        (Scheme.Modules.pushforward π₁).map ((Scheme.Modules.pullback e).map (θ.hom.app k)) ≫
        (Scheme.Modules.pushforward π₁).map (cT.hom.app k) := by
  refine (congrArg (Scheme.Modules.pushforward π₁).map
    (show _ = _ ≫ _ ≫ _ ≫ _ from rfl)).trans ?_
  let F := Scheme.Modules.pushforward π₁
  exact (F.map_comp _ _).trans (congrArg (F.map _ ≫ ·)
    ((F.map_comp _ _).trans (congrArg (F.map _ ≫ ·) (F.map_comp _ _))))

/-- **Carrying a homogeneous-section map along a congruence, a composite and two isomorphisms.**
Let `pc = e ≫ bc` with `bc : P₂ ⟶ P` over `hs : Y' ⟶ Y` and `e : P₁ ⟶ P₂` over `Y'`, let `θ` and
`cT` be isomorphisms of sheaves of graded algebras `bc^*G ≅ T₂` and `e^*T₂ ≅ T₁`.  If `θ` carries
the base change of `ψ` along `bc` to `ψ₂`, and `cT` carries `Φ ≫ ψ₂` followed by the unit of
`e^* ⊣ e_*` to `ψ₁`, then the composite `pc^*G ≅ (e ≫ bc)^*G ≅ e^*bc^*G ≅ e^*T₂ ≅ T₁` carries
`Φ` followed by the base change of `ψ` along `pc` to `ψ₁`. -/
theorem basePsi_comp_pullbackGradedAlgebraChain {Y Y' P P₁ P₂ : Scheme.{u}} (π : P ⟶ Y)
    (π₁ : P₁ ⟶ Y') (π₂ : P₂ ⟶ Y') (hs : Y' ⟶ Y) (pc : P₁ ⟶ P) (e : P₁ ⟶ P₂) (bc : P₂ ⟶ P)
    (hpc : pc = e ≫ bc) (hpcT : pc ≫ π = π₁ ≫ hs) (hbc : bc ≫ π = π₂ ≫ hs) (he : e ≫ π₂ = π₁)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P.toRingedSpace))
    (T₂ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P₂.toRingedSpace))
    (T₁ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf P₁.toRingedSpace))
    (θ : pbAlgS bc G ≅ T₂) (cT : pbAlgS e T₂ ≅ T₁) {M : Y.Modules} {M₁ : Y'.Modules} (k : ℤ)
    (Φk : M₁ ⟶ (Scheme.Modules.pullback hs).obj M)
    (ψ : M ⟶ (Scheme.Modules.pushforward π).obj (G.piece k))
    (ψ₂ : (Scheme.Modules.pullback hs).obj M ⟶ (Scheme.Modules.pushforward π₂).obj (T₂.piece k))
    (ψ₁ : M₁ ⟶ (Scheme.Modules.pushforward π₁).obj (T₁.piece k))
    (hθ : basePsi π π₂ hs bc hbc ψ ≫ (Scheme.Modules.pushforward π₂).map (θ.hom.app k) = ψ₂)
    (ψc : M₁ ⟶ (Scheme.Modules.pushforward π₁).obj ((Scheme.Modules.pullback e).obj (T₂.piece k)))
    (hψc : ψc = Φk ≫ ψ₂ ≫ (Scheme.Modules.pushforward π₂).map
        ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app (T₂.piece k)) ≫
        (Scheme.Modules.pushforwardComp e π₂).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr he).hom.app _)
    (hcT : ψc ≫ (Scheme.Modules.pushforward π₁).map (cT.hom.app k) = ψ₁) :
    Φk ≫ basePsi π π₁ hs pc hpcT ψ ≫ (Scheme.Modules.pushforward π₁).map
      ((GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G hpc ≪≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G e bc).symm ≪≫
        Stacks.RingedSpace.pullbackGradedAlgebraMapIso _ θ ≪≫ cT).hom.app k) = ψ₁ := by
  have h' : (e ≫ bc) ≫ π = π₁ ≫ hs := by rw [Category.assoc, hbc, ← Category.assoc, he]
  refine (congrArg (fun x => Φk ≫ basePsi π π₁ hs pc hpcT ψ ≫ x)
    (pushforward_map_congrComp_hom_app π₁ pc e bc hpc G T₂ T₁ θ cT k)).trans ?_
  rw [← hcT, hψc, ← hθ]
  simp only [Category.assoc]
  refine congrArg (Φk ≫ ·) ?_
  rw [← Category.assoc (basePsi π π₁ hs pc hpcT ψ), basePsi_congr π π₁ hs pc hpcT ψ hpc h',
    ← Category.assoc (basePsi π π₁ hs (e ≫ bc) h' ψ),
    basePsi_comp_unit π π₂ hs bc hbc ψ π₁ e he h']
  simp only [Category.assoc]
  refine congrArg (basePsi π π₂ hs bc hbc ψ ≫ ·) ?_
  exact pushforward_unit_comp_pushforward_map_pullback_map e π₂ π₁ he (θ.hom.app k) _

section CongrBaseChange

open Stacks.AlgebraicGeometry.RelativeProjBridge

variable {Y Y' : Scheme.{u}} (A : SheafGradedAlgebra Y) (hs : Y' ⟶ Y) {A₁ : SheafGradedAlgebra Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (pc : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme)
  (hpc : pc = (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs)

/-- **The twists of Tag 01NR along a restriction followed by a base change.**  Let `hs : Y' ⟶ Y`,
`A₁` a graded algebra on `Y'` with an isomorphism `Φ : A₁ ≅ hs^*A`, and `pc = e ≫ bc` with
`e = relativeProjCongr Φ : Proj(A₁) ≅ Proj(hs^*A)` and `bc` the base-change morphism of Tag 01O3.
The isomorphism `pc^*𝒪(*) ≅ e^*bc^*𝒪(*) ≅ e^*𝒪_{Proj(hs^*A)}(*) ≅ 𝒪_{Proj(A₁)}(*)` of sheaves of
`ℤ`-graded algebras assembled from Tag 01O3's `θ` (`pulledTwistIso`) and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.congrTwistIso`. -/
@[ega "II 2.8.11" "more general"]
def congrBaseChangeTwistIso :
    pbAlgS pc (Tag07ZGTwist.twistAlgebra A) ≅ Tag07ZGTwist.twistAlgebra A₁ :=
  GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _ hpc ≪≫
    (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _ _ _).symm ≪≫
    Stacks.RingedSpace.pullbackGradedAlgebraMapIso _ (pulledTwistIso A hs) ≪≫
    RelativeProjQcohSheaf.congrTwistIso Φ hΦ

/-- The homogeneous-section maps of the pulled-back twists `pc^*𝒪(k)`: `Φ`, followed by the base
change along the square of `pc` over `hs` of Tag 01NR's `ψ` for `A`. -/
def congrBaseChangePsi
    (hpcT : pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs) (k : ℕ) :
    A₁.piece (k : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A₁).toBase).obj
      ((pbAlgS pc (Tag07ZGTwist.twistAlgebra A)).piece (k : ℤ)) :=
  (RelativeProjQcohSheaf.congrHom Φ).app (k : ℤ) ≫
    basePsi (relativeProj A).toBase (relativeProj A₁).toBase hs pc hpcT
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k)

/-- **`congrBaseChangeTwistIso` carries `congrBaseChangePsi` to Tag 01NR's `ψ` for `A₁`**, in
every degree `k ≥ 0`. -/
theorem congrBaseChangePsi_comp_congrBaseChangeTwistIso
    (hpcT : pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs) (k : ℕ) :
    congrBaseChangePsi A hs Φ pc hpcT k ≫
        (Scheme.Modules.pushforward (relativeProj A₁).toBase).map
          ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (k : ℤ)) =
      (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁).ψ k :=
  (Category.assoc _ _ _).trans
    (basePsi_comp_pullbackGradedAlgebraChain (relativeProj A).toBase
      (relativeProj A₁).toBase (relativeProj (A.pullback hs)).toBase hs pc
      (RelativeProjQcohSheaf.relativeProjCongr Φ hΦ).hom (baseChangeHom A hs) hpc hpcT
      (baseChangeHom_comp_toBase A hs)
      (RelativeProjQcohSheaf.relativeProjCongr_hom_comp_toBase Φ hΦ)
      (Tag07ZGTwist.twistAlgebra A) _ _ (pulledTwistIso A hs)
      (RelativeProjQcohSheaf.congrTwistIso Φ hΦ) (k : ℤ)
      ((RelativeProjQcohSheaf.congrHom Φ).app (k : ℤ))
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k) _ _
      (TwistExistenceBasis.glueIso_psi (isBasis_baseChangeBasis hs)
        (isAffineOpen_of_mem_baseChangeBasis hs) (pulledBasisData A hs)
        (TwistExistenceBasis.BasisTwistData.ofTwistData
          (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback hs))) k) _
      rfl (RelativeProjQcohSheaf.congrPsi_comp_congrTwistIso Φ hΦ k))

/-- For `pc'' = pc' ≫ pc` lying over `hs' ≫ hs` and `Φ''k` the composite of `Φ'k` and the
pullback of `Φk`, the base change of `ψ` along `pc''` followed by the congruence and composition
isomorphisms and the maps `Th` and `T'h` is the base change along `pc'` of the base change of `ψ`
along `pc` followed by `Th`, followed by `T'h`. -/
theorem basePsi_comp_chain {Y Y' Y'' P P' P'' : Scheme.{u}} (p : P ⟶ Y) (p' : P' ⟶ Y')
    (p'' : P'' ⟶ Y'') (hs : Y' ⟶ Y) (hs' : Y'' ⟶ Y') (pc : P' ⟶ P) (pc' : P'' ⟶ P')
    (pc'' : P'' ⟶ P) (hcomp : pc'' = pc' ≫ pc) (hpcT : pc ≫ p = p' ≫ hs)
    (hpcT' : pc' ≫ p' = p'' ≫ hs') (hpcT'' : pc'' ≫ p = p'' ≫ (hs' ≫ hs))
    (hpcc : (pc' ≫ pc) ≫ p = p'' ≫ (hs' ≫ hs)) {M : Y.Modules} {O : P.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward p).obj O) {M' : Y'.Modules} {M'' : Y''.Modules}
    {O' : P'.Modules} {O'' : P''.Modules}
    (Φk : M' ⟶ (Scheme.Modules.pullback hs).obj M)
    (Φ'k : M'' ⟶ (Scheme.Modules.pullback hs').obj M')
    (Φ''k : M'' ⟶ (Scheme.Modules.pullback (hs' ≫ hs)).obj M)
    (Th : (Scheme.Modules.pullback pc).obj O ⟶ O')
    (T'h : (Scheme.Modules.pullback pc').obj O' ⟶ O'')
    (hΦc : Φ''k = Φ'k ≫ (Scheme.Modules.pullback hs').map Φk ≫
      (Scheme.Modules.pullbackComp hs' hs).hom.app M) :
    (Φ''k ≫ basePsi p p'' (hs' ≫ hs) pc'' hpcT'' ψ) ≫
        (Scheme.Modules.pushforward p'').map ((Scheme.Modules.pullbackCongr hcomp).hom.app O) ≫
        (Scheme.Modules.pushforward p'').map ((Scheme.Modules.pullbackComp pc' pc).inv.app O) ≫
        (Scheme.Modules.pushforward p'').map ((Scheme.Modules.pullback pc').map Th) ≫
        (Scheme.Modules.pushforward p'').map T'h =
      (Φ'k ≫ basePsi p' p'' hs' pc' hpcT'
        ((Φk ≫ basePsi p p' hs pc hpcT ψ) ≫ (Scheme.Modules.pushforward p').map Th)) ≫
        (Scheme.Modules.pushforward p'').map T'h := by
  rw [basePsi_comp_pushforward_map, basePsi_pullback_map_comp, hΦc]
  simp only [Category.assoc]
  refine congrArg (Φ'k ≫ ·) ?_
  refine congrArg ((Scheme.Modules.pullback hs').map Φk ≫ ·) ?_
  rw [← Category.assoc (basePsi p p'' (hs' ≫ hs) pc'' hpcT'' ψ),
    basePsi_congr p p'' (hs' ≫ hs) pc'' hpcT'' ψ hcomp hpcc,
    ← basePsi_comp (p := p) (ψ₀ := ψ) (p₂ := p') (p₁ := p'') (g₂ := hs) (g₁ := hs') (f₂ := pc)
      (f₁ := pc') (h₂ := hpcT) (h₁ := hpcT') (h₁₂ := hpcc)]
  simp only [Category.assoc]

/-- **The comparison of twists composes.**  For `hs' : Y'' ⟶ Y'`, `hs : Y' ⟶ Y`,
isomorphisms `Φ : A' ≅ hs^*A`, `Φ' : A'' ≅ hs'^*A'` and `Φ'' : A'' ≅ (hs' ≫ hs)^*A` compatible
with the composition of inverse images (`hΦc`), and `pc'' = pc' ≫ pc`, the comparison of twists
along `pc''` is the comparison along `pc` pulled back along `pc'`, followed by the comparison
along `pc'`. -/
theorem congrBaseChangeTwistIso_comp {Y'' : Scheme.{u}} (hs' : Y'' ⟶ Y') (hs'' : Y'' ⟶ Y)
    (hhs : hs' ≫ hs = hs'') {A'' : SheafGradedAlgebra Y''}
    (Φ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A'')
      (situationAlgebra (A₁.pullback hs')))
    (hΦ' : ∀ n : ℤ, IsIso (Φ'.app n))
    (Φ'' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A'')
      (situationAlgebra (A.pullback hs'')))
    (hΦ'' : ∀ n : ℤ, IsIso (Φ''.app n))
    (hΦc : ∀ k : ℕ, (RelativeProjQcohSheaf.congrHom Φ'').app (k : ℤ) =
      (RelativeProjQcohSheaf.congrHom Φ').app (k : ℤ) ≫
        (Scheme.Modules.pullback hs').map ((RelativeProjQcohSheaf.congrHom Φ).app (k : ℤ)) ≫
        ModuleLimits.canHom hs' hs hs'' hhs (A.piece (k : ℤ)))
    (pc' : (relativeProj A'').scheme ⟶ (relativeProj A₁).scheme)
    (hpc' : pc' = (relativeProjCongr Φ' hΦ').hom ≫ baseChangeHom A₁ hs')
    (pc'' : (relativeProj A'').scheme ⟶ (relativeProj A).scheme)
    (hpc'' : pc'' = (relativeProjCongr Φ'' hΦ'').hom ≫ baseChangeHom A hs'')
    (hcomp : pc'' = pc' ≫ pc)
    (hpcT : pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs)
    (hpcT' : pc' ≫ (relativeProj A₁).toBase = (relativeProj A'').toBase ≫ hs') :
    congrBaseChangeTwistIso A hs'' Φ'' hΦ'' pc'' hpc'' =
      GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _ hcomp ≪≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _ pc' pc).symm ≪≫
        Stacks.RingedSpace.pullbackGradedAlgebraMapIso _
          (congrBaseChangeTwistIso A hs Φ hΦ pc hpc) ≪≫
        congrBaseChangeTwistIso A₁ hs' Φ' hΦ' pc' hpc' := by
  subst hhs
  have hΦc' : ∀ k : ℕ, (RelativeProjQcohSheaf.congrHom Φ'').app (k : ℤ) =
      (RelativeProjQcohSheaf.congrHom Φ').app (k : ℤ) ≫
        (Scheme.Modules.pullback hs').map ((RelativeProjQcohSheaf.congrHom Φ).app (k : ℤ)) ≫
        (Scheme.Modules.pullbackComp hs' hs).hom.app (A.piece (k : ℤ)) := fun k =>
    (hΦc k).trans (congrArg (_ ≫ _ ≫ ·) (Category.comp_id _))
  have hpcT'' : pc'' ≫ (relativeProj A).toBase = (relativeProj A'').toBase ≫ (hs' ≫ hs) := by
    rw [hcomp, Category.assoc, hpcT, ← Category.assoc, hpcT', Category.assoc]
  refine TwistExistence.iso_ext_of_psi (GluedTwistAlgebra.twistDataOfGradedAlgebra A'')
    (congrBaseChangePsi A (hs' ≫ hs) Φ'' pc'' hpcT'')
    (congrBaseChangePsi_comp_congrBaseChangeTwistIso A (hs' ≫ hs) Φ'' hΦ'' pc'' hpc'' hpcT'')
    fun k => ?_
  have hpcc : (pc' ≫ pc) ≫ (relativeProj A).toBase = (relativeProj A'').toBase ≫ (hs' ≫ hs) := by
    rwa [← hcomp]
  refine (congrArg (congrBaseChangePsi A (hs' ≫ hs) Φ'' pc'' hpcT'' k ≫ ·)
    (pushforward_map_congrComp_hom_app _ pc'' pc' pc hcomp _ _ _ _ _ _)).trans ?_
  rw [← congrBaseChangePsi_comp_congrBaseChangeTwistIso A₁ hs' Φ' hΦ' pc' hpc' hpcT' k]
  unfold congrBaseChangePsi
  rw [← congrBaseChangePsi_comp_congrBaseChangeTwistIso A hs Φ hΦ pc hpc hpcT k]
  unfold congrBaseChangePsi
  exact basePsi_comp_chain (relativeProj A).toBase (relativeProj A₁).toBase
    (relativeProj A'').toBase hs hs' pc pc' pc'' hcomp hpcT hpcT' hpcT'' hpcc
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k) _ _ _ _ _ (hΦc' k)

end CongrBaseChange

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The comparison morphism of Stacks 084B (3) lies over `h`: it commutes with the structure
morphisms of the two relative homogeneous spectra. -/
theorem projComparison_comp_toBase {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (g : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra g h) ≫
        (relativeProj (s.shrink.pointAlgebra Z g)).toBase =
      (relativeProj (s.shrink.pointAlgebra Z' (yoneda.map h ≫ g))).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h := by
  refine (congrArg (· ≫ (relativeProj (s.shrink.pointAlgebra Z g)).toBase)
    (s.isPullback_projComparison g h).2.2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((s.quadrupleRestriction.restrictProjIso g h).hom ≫ ·)
    (baseChangeHom_comp_toBase (s.shrink.pointAlgebra Z g)
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫
    (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h)
    (relativeProjCongr_hom_comp_toBase (A₁ := s.shrink.pointAlgebra Z' (yoneda.map h ≫ g))
      (A₂ := (s.shrink.pointAlgebra Z g).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))
      (s.quadrupleRestriction.restrict h g (yoneda.map h ≫ g) rfl)
      (s.quadrupleRestriction.isIso_restrict_app h g _ rfl))

/-! ### The comparison of twists at an arbitrary pair of points, and its cocycle -/

section PointComparison

variable {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
  (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
  (pc : (relativeProj (s.shrink.pointAlgebra V v)).scheme ⟶
    (relativeProj (s.shrink.pointAlgebra U u)).scheme)
  (hpc : pc = (relativeProjCongr (A₁ := s.shrink.pointAlgebra V v)
      (A₂ := (s.shrink.pointAlgebra U u).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
      (s.quadrupleRestriction.restrict k u v hv)
    (s.quadrupleRestriction.isIso_restrict_app k u v hv)).hom ≫
      baseChangeHom (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))

/-- **The comparison of twists along a morphism lying over `k`.**  For a morphism `k : V ⟶ U` of
test objects, points `u` of `X` at `U` and `v = u ∘ k` at `V`, and a morphism
`pc : Proj_V(v^*𝒜) ⟶ Proj_U(u^*𝒜)` which is the identification of the restrictions followed by
the base-change morphism of Tag 01O3 (`hpc`), the isomorphism
`pc^*(⨁_n 𝒪_{Proj_U(u^*𝒜)}(n)) ≅ ⨁_n 𝒪_{Proj_V(v^*𝒜)}(n)` of sheaves of graded algebras.
The comparison morphism of Stacks 084B (3) is the case `pc = projComparison g h`, `v = g ∘ h`. -/
def pointTwistComparison :
    pbAlgS pc (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)) ≅
      Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v) :=
  congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra V v) (s.quadrupleRestriction.restrict k u v hv)
    (s.quadrupleRestriction.isIso_restrict_app k u v hv) pc hpc

/-- The homogeneous-section maps of the pulled-back twists `pc^*𝒪(*)` along a morphism lying
over `k`. -/
def pointTwistComparisonPsi
    (hpcT : pc ≫ (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) (n : ℕ) :
    (s.shrink.pointAlgebra V v).piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj (s.shrink.pointAlgebra V v)).toBase).obj
        ((pbAlgS pc (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u))).piece (n : ℤ)) :=
  congrBaseChangePsi (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra V v) (s.quadrupleRestriction.restrict k u v hv) pc hpcT n

/-- **`pointTwistComparison` carries `ψ` to `ψ`.** -/
theorem pointTwistComparisonPsi_comp_pointTwistComparison
    (hpcT : pc ≫ (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) (n : ℕ) :
    s.pointTwistComparisonPsi k u v hv pc hpcT n ≫
        (Scheme.Modules.pushforward (relativeProj (s.shrink.pointAlgebra V v)).toBase).map
          ((s.pointTwistComparison k u v hv pc hpc).hom.app (n : ℤ)) =
      (GluedTwistAlgebra.twistDataOfGradedAlgebra (s.shrink.pointAlgebra V v)).ψ n := by
  have e1 : s.pointTwistComparison k u v hv pc hpc = congrBaseChangeTwistIso
      (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
          (A₁ := s.shrink.pointAlgebra V v)
      (s.quadrupleRestriction.restrict k u v hv)
      (s.quadrupleRestriction.isIso_restrict_app k u v hv) pc hpc := rfl
  have e2 : s.pointTwistComparisonPsi k u v hv pc hpcT n = congrBaseChangePsi
      (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
          (A₁ := s.shrink.pointAlgebra V v)
      (s.quadrupleRestriction.restrict k u v hv) pc hpcT n := rfl
  rw [e1, e2]
  exact congrBaseChangePsi_comp_congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
      (A₁ := s.shrink.pointAlgebra V v) (s.quadrupleRestriction.restrict k u v hv)
    (s.quadrupleRestriction.isIso_restrict_app k u v hv) pc hpc hpcT n

/-- **The cocycle of the comparisons of twists.**  For `k' : W ⟶ V`, `k : V ⟶ U`,
points `u`, `v = u ∘ k`, `w = v ∘ k'` and morphisms `pc`, `pc'`, `pc''` lying over `k`, `k'` and
`k' ≫ k` with `pc'' = pc' ≫ pc`, the comparison of twists along `pc''` is the comparison along
`pc` pulled back along `pc'`, followed by the comparison along `pc'`. -/
theorem pointTwistComparison_comp {W : BigFppfOver s.site s.base s.containsBase} (k' : W ⟶ V)
    (w : yoneda.obj W ⟶ s.space.1) (hw : yoneda.map k' ≫ v = w)
    (hw'' : yoneda.map (k' ≫ k) ≫ u = w)
    (pc' : (relativeProj (s.shrink.pointAlgebra W w)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra V v)).scheme)
    (hpc' : pc' = (relativeProjCongr (A₁ := s.shrink.pointAlgebra W w)
      (A₂ := (s.shrink.pointAlgebra V v).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k'))
      (s.quadrupleRestriction.restrict k' v w hw)
      (s.quadrupleRestriction.isIso_restrict_app k' v w hw)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra V v)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k'))
    (pc'' : (relativeProj (s.shrink.pointAlgebra W w)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (hpc'' : pc'' = (relativeProjCongr (A₁ := s.shrink.pointAlgebra W w)
      (A₂ := (s.shrink.pointAlgebra U u).pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (k' ≫ k)))
      (s.quadrupleRestriction.restrict (k' ≫ k) u w hw'')
      (s.quadrupleRestriction.isIso_restrict_app (k' ≫ k) u w hw'')).hom ≫
        baseChangeHom (s.shrink.pointAlgebra U u)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (k' ≫ k)))
    (hcomp : pc'' = pc' ≫ pc)
    (hpcT : pc ≫ (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (hpcT' : pc' ≫ (relativeProj (s.shrink.pointAlgebra V v)).toBase =
      (relativeProj (s.shrink.pointAlgebra W w)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k') :
    s.pointTwistComparison (k' ≫ k) u w hw'' pc'' hpc'' =
      pullbackGradedAlgebraCongrIso _ hcomp ≪≫
        (pullbackGradedAlgebraCompIso _ pc' pc).symm ≪≫
        Stacks.RingedSpace.pullbackGradedAlgebraMapIso _
          (s.pointTwistComparison k u v hv pc hpc) ≪≫
        s.pointTwistComparison k' v w hw pc' hpc' :=
  congrBaseChangeTwistIso_comp (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra V v) (s.quadrupleRestriction.restrict k u v hv)
    (s.quadrupleRestriction.isIso_restrict_app k u v hv) pc hpc
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k')
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (k' ≫ k))
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map_comp k' k).symm
        (A'' := s.shrink.pointAlgebra W w)
    (s.quadrupleRestriction.restrict k' v w hw)
    (s.quadrupleRestriction.isIso_restrict_app k' v w hw)
    (s.quadrupleRestriction.restrict (k' ≫ k) u w hw'')
    (s.quadrupleRestriction.isIso_restrict_app (k' ≫ k) u w hw'')
    (fun n => congrArg (fun Ψ => SheafOfModules.GradedAlgebra.UnitalHom.app Ψ (n : ℤ))
      (s.quadrupleRestriction.restrict_comp k k' u v w hv hw hw''))
    pc' hpc' pc'' hpc'' hcomp hpcT hpcT'

/-- For `h : Z' ⟶ Z`, a point `g` at `Z` and `f' = g ∘ h`, the comparison morphism of
Stacks 084B (3) precomposed with the identification of the two fibres is the identification of
the restrictions followed by the base-change morphism of Tag 01O3. -/
theorem toScheme_map_eqToHom_projComparison {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (g : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) (f' : yoneda.obj Z' ⟶ s.space.1)
    (hf : yoneda.map h ≫ g = f') :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (eqToHom (congrArg (s.relativeProjPoints.fibre Z') hf).symm ≫
          s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra g h) =
      (relativeProjCongr (A₁ := s.shrink.pointAlgebra Z' f')
        (A₂ := (s.shrink.pointAlgebra Z g).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h))
        (s.quadrupleRestriction.restrict h g f' hf)
        (s.quadrupleRestriction.isIso_restrict_app h g f' hf)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra Z g)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h) := by
  subst hf
  exact (congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map
    (Category.id_comp _)).trans (s.isPullback_projComparison g h).2.2

/-- The comparison morphism read at an equal point commutes with the structure morphisms. -/
theorem toScheme_map_eqToHom_projComparison_comp_toBase
    {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (g : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) (f' : yoneda.obj Z' ⟶ s.space.1)
    (hf : yoneda.map h ≫ g = f') :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (eqToHom (congrArg (s.relativeProjPoints.fibre Z') hf).symm ≫
          s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra g h) ≫
        (relativeProj (s.shrink.pointAlgebra Z g)).toBase =
      (relativeProj (s.shrink.pointAlgebra Z' f')).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map h := by
  subst hf
  exact (congrArg (· ≫ (relativeProj (s.shrink.pointAlgebra Z g)).toBase)
    (congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map
      (Category.id_comp _))).trans (s.projComparison_comp_toBase g h)

end PointComparison

end RelativeProjSituation

end AlgebraicGeometry.Space

end
