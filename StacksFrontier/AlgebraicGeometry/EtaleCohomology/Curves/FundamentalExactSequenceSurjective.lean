module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequencePresheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldIso
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.EtaleMorphism
public import StacksFrontier.CategoryTheory.Sites.SigmaPresheafLocallyBijective

/-!
# Surjectivity of the divisor map of Stacks 03RI

placeholder
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### The generic point of a curve is not closed -/

/-- **The generic point of a curve is not a closed point.** Were it closed its closure, which is
the whole space, would be a single point, and a one-point space is discrete, hence of topological
Krull dimension zero rather than one. -/
theorem ne_genericPoint_of_mem_closedPoints {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsCurve k f] {y : Y} (hy : y ∈ closedPoints Y) :
    y ≠ genericPoint Y := by
  intro hyg
  have hcl : IsClosed ({y} : Set Y) := hy
  have huniv : ({y} : Set Y) = Set.univ := by
    rw [← hcl.closure_eq, hyg]
    exact genericPoint_spec Y
  have hall : ∀ a : Y, a = y := fun a =>
    Set.mem_singleton_iff.1 (huniv ▸ Set.mem_univ a)
  have : DiscreteTopology ↥Y := discreteTopology_iff_isOpen_singleton.2 fun z => by
    rw [show ({z} : Set Y) = Set.univ by rw [hall z]; exact huniv]
    exact isOpen_univ
  have h1 : topologicalKrullDim ↥Y ≤ 0 := topologicalKrullDim_zero_of_discreteTopology ↥Y
  rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)] at h1
  exact absurd h1 (by decide)

/-! ### Open subschemes as objects of the small étale site -/

section OpenSub

variable {X : Scheme.{u}} (W : X.Etale)

/-- **An open subscheme of an étale `X`-scheme, as an object of the small étale site**: an open
immersion is étale and étale morphisms compose. -/
def etaleOpenSub (O : W.left.Opens) : X.Etale :=
  Scheme.Etale.mk (O.ι ≫ W.hom)

/-- The inclusion of an open subscheme, as a morphism of the small étale site. -/
def etaleOpenSubHom (O : W.left.Opens) : etaleOpenSub W O ⟶ W :=
  MorphismProperty.Over.homMk O.ι

/-- The underlying scheme of `etaleOpenSub W O` is the open subscheme `O` of `W.left`. -/
@[simp]
theorem etaleOpenSub_left (O : W.left.Opens) : (etaleOpenSub W O).left = O.toScheme :=
  rfl

/-- The underlying morphism of schemes of `etaleOpenSubHom W O` is the open immersion `O.ι`. -/
@[simp]
theorem etaleOpenSubHom_left (O : W.left.Opens) : (etaleOpenSubHom W O).left = O.ι :=
  rfl

/-- The structure morphism of `etaleOpenSub W O` to `X` is `O.ι ≫ W.hom`. -/
@[simp]
theorem etaleOpenSub_hom (O : W.left.Opens) : (etaleOpenSub W O).hom = O.ι ≫ W.hom :=
  rfl

end OpenSub


/-! ### Skyscraper sections over an object with empty fibre -/

/-- **The sections of `(i_x)_* 𝐙` over an étale `X`-scheme whose fibre over `x` is empty are
zero.** -/
theorem subsingleton_integerSkyscraper_obj {X : Scheme.{u}} (x : X) (V : X.Etale)
    [IsEmpty ↥((smallEtaleBaseChange (X.fromSpecResidueField x)).obj V).left] :
    Subsingleton ↥((integerSkyscraper.{u, v} X x).obj.obj (op V)) := by
  have hinj : Function.Injective
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x V).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  exact ⟨fun a b => hinj (LocallyConstant.ext fun y => isEmptyElim y)⟩


/-! ### The order of vanishing of a pulled-back rational function -/

section Ord

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]

/-- **The order of vanishing on an étale `X`-scheme of a rational function pulled back from
`X`.** If a section of `j_* 𝐆_{m,η}` over `V` is, as a rational function on `V`, the restriction
of a rational function `c` on `X`, then its order of vanishing at a point of `V` is the order of
vanishing of `c` at the image point. -/
theorem etaleGenericFibreOrd_eq_ord (V : X.Etale) [AlgebraicGeometry.IsIntegral V.left]
    [IsLocallyNoetherian V.left] [IsDominant V.hom]
    (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) (c : ↥X.functionField)
    (hac : genericFibreToFunctionField (X := X) (U := V.left) V.hom
        (a : Γ(pullback V.hom (genericPointInclusion X), ⊤)) =
      dominantFunctionFieldMap (X := V.left) (S := X) V.hom c) (y : V.left) :
    etaleGenericFibreOrd.{u} V y (Additive.ofMul a) = X.ord c (V.hom.base y) := by
  refine (genericFibreOrd_apply (X := X) (U := V.left) V.hom y (Additive.ofMul a)).trans ?_
  show Scheme.ord (genericFibreToFunctionField (X := X) (U := V.left) V.hom
    (a : Γ(pullback V.hom (genericPointInclusion X), ⊤))) y = _
  rw [hac]
  exact Stacks.Chow.ord_dominantFunctionFieldMap_eq_ord_base_of_etale (X := X) (Z := V.left)
    V.hom c y

end Ord

/-! ### From a divisor on sections to a point of the image sieve -/

section Image

attribute [local instance] Classical.decEq

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsCurve k fX]
  [Smooth fX]

/-- **A section of `j_* 𝐆_{m,η}` over `V` whose divisor is the restriction of a section of one
summand witnesses that summand section as locally in the image of the second map of the
fundamental exact sequence.** -/
theorem imageSieve_closedPointDivisorMap_of_divisorSections_eq {W V : X.Etale} (res : V ⟶ W)
    [AlgebraicGeometry.IsIntegral V.left] [CompactSpace V.left] [IsLocallyNoetherian V.left]
    [NoetherianSpace V.left] (x : closedPoints X)
    (β : (closedPointSkyscraper.{u, v} X x).obj.obj (op W))
    (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ)
    (hcore : genericFibreDivisorSections.{u, v} V (Additive.ofMul a) =
      DirectSum.of (fun y : closedPoints X =>
          ((closedPointSkyscraper.{u, v} X y).obj.obj (op V) : Type _)) x
        ((closedPointSkyscraper.{u, v} X x).obj.map res.op β)) :
    Presheaf.imageSieve (closedPointDivisorMap.{u, v} fX).hom
      ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) res := by
  refine ⟨ULift.up (Additive.ofMul a), ?_⟩
  have hd : (closedPointDivisorMap.{u, v} fX).hom.app (op V) (ULift.up (Additive.ofMul a)) =
      (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op V)
        ((genericFibreDivisorIntegral.{u, v} fX).app (op ⟨V, ⟨inferInstance, inferInstance⟩⟩)
          (ULift.up (Additive.ofMul a))) :=
    ConcreteCategory.congr_hom
      (closedPointDivisorMap_app.{u, v} fX ⟨V, ⟨inferInstance, inferInstance⟩⟩) _
  have h1 : (closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op V)
        ((closedPointSkyscraper.{u, v} X x).obj.map res.op β) =
      (closedPointDivisorSheaf.{u, v} X).obj.map res.op
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op W) β) :=
    ConcreteCategory.congr_hom ((closedPointDivisorSheaf.ι.{u, v} X x).hom.naturality res.op) β
  have h2 : (closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op V)
        ((closedPointSkyscraper.{u, v} X x).obj.map res.op β) =
      (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op V)
        ((Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) x).app (op V)
          ((closedPointSkyscraper.{u, v} X x).obj.map res.op β)) :=
    (ConcreteCategory.congr_hom
      (congr_app (closedPointDivisorSheaf.ι_fromPresheafCoproduct.{u, v} X x) (op V)) _).symm
  have h3 : (genericFibreDivisorIntegral.{u, v} fX).app (op ⟨V, ⟨inferInstance, inferInstance⟩⟩)
        (ULift.up (Additive.ofMul a)) =
      (Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) x).app (op V)
        ((closedPointSkyscraper.{u, v} X x).obj.map res.op β) := by
    refine (genericFibreDivisorPresheafMap_apply.{u, v} V (ULift.up (Additive.ofMul a))).trans ?_
    refine (congrArg (DirectSum.toAddMonoid fun y : closedPoints X =>
      ((Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) y).app
        (op V)).hom) hcore).trans ?_
    exact DirectSum.toAddMonoid_of _ x _
  exact hd.trans (((congrArg
    ((closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X).app (op V)) h3).trans
      h2.symm).trans h1)

end Image

end Stacks.EtaleCohomology

end
