module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion

/-!
# Functoriality of the sheaves of relative differential forms in the square

`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` attaches to a commutative square

```
X' → X
↓    ↓
S' → S
```

the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative differential `n`-forms. Those maps
compose: for two horizontally composable commutative squares

```
X'' → X' → X
 ↓     ↓    ↓
S'' → S' → S
```

the map of the outer square is the map of the right-hand square, pulled back along the upper
edge of the left-hand square, followed by the map of the left-hand square — read through the
coherence isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp` between `(f' ≫ f)^*` and
`f'^* ∘ f^*`.

## Main results

* `SheafOfModules.GradedAlgebra.pullbackComparison_comp_unitalHom`: the canonical comparison of
  Stacks 01CI absorbs a unital homomorphism of sheaves of graded algebras on the target.
* `SheafOfModules.GradedAlgebra.pullbackComparison_comp`: the comparison of Stacks 01CI is a
  cocycle: the comparison of a composite of morphisms of ringed spaces is the composite of the
  two comparisons.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_eq_pullbackComparison`: the
  canonical map on relative differential forms is itself a comparison of Stacks 01CI, for the
  degree-one generator supplied by the canonical map on relative differentials.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_pullbackComp` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp`: the canonical maps of two
  horizontally composable commutative squares compose, on relative differentials and on relative
  differential forms.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe t a v₁ u₁ u

namespace SheafOfModules.Hom

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Equal morphisms of sheaves of modules agree on every local section. -/
theorem congr_val_app {M N : SheafOfModules.{a} R} {φ ψ : M ⟶ N} (h : φ = ψ) (U : Cᵒᵖ)
    (x : M.val.obj U) : φ.val.app U x = ψ.val.app U x := by rw [h]

end SheafOfModules.Hom

namespace SheafOfModules.GradedAlgebra

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {F : SheafOfModules.{u} (structureSheafRing Y)}
  {A : GradedAlgebra.{u, u} (structureSheafRing Y)} {ι : F ⟶ A.piece 1}
  {B : GradedAlgebra.{u, u} (structureSheafRing X)}
  {κ : (modulePullback f).obj F ⟶ B.piece 1} (hA : IsExteriorAlgebra A ι)

/-- The canonical comparison depends on the degree-one generator of the target only through its
value, not through the proof that it is square-zero. -/
theorem pullbackComparison_congr {κ₁ κ₂ : (modulePullback f).obj F ⟶ B.piece 1} (h : κ₁ = κ₂)
    (hκ₁ : SquareZero κ₁) (hκ₂ : SquareZero κ₂) (n : ℤ) :
    pullbackComparison f hA hκ₁ n = pullbackComparison f hA hκ₂ n := by
  subst h; rfl

/-- The canonical comparison of Stacks 01CI absorbs a unital homomorphism: composing the
comparison `f^*(A_n) ⟶ B_n` attached to a square-zero generator `κ` of `B` with a unital
homomorphism `Φ : B ⟶ D` of sheaves of graded algebras gives the comparison attached to the
square-zero generator `κ ≫ Φ₁` of `D`. -/
theorem pullbackComparison_comp_unitalHom (hκ : SquareZero κ)
    {D : GradedAlgebra.{u, u} (structureSheafRing X)} (Φ : UnitalHom B D) (n : ℤ) :
    pullbackComparison f hA hκ n ≫ Φ.app n =
      pullbackComparison f hA (hκ.compUnitalHom Φ) n := by
  refine pullbackComparison_unique f hA (hκ.compUnitalHom Φ)
    (fun m => pullbackComparison f hA hκ m ≫ Φ.app m) (fun i j U a b => ?_) (fun U => ?_)
    (fun U s => ?_) n
  · exact (congrArg (fun z => (Φ.app (i + j)).val.app ((opensMap f).op.obj U) z)
      (pullbackComparison_mul f hA hκ i j U a b)).trans (Φ.map_mul i j _ _ _)
  · exact (congrArg (fun z => (Φ.app 0).val.app ((opensMap f).op.obj U) z)
      (pullbackComparison_one f hA hκ U)).trans (Φ.map_one _)
  · exact congrArg (fun z => (Φ.app 1).val.app ((opensMap f).op.obj U) z)
      (pullbackComparison_generator f hA hκ U s)

end RingedSpace

section Composition

open AlgebraicGeometry RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {Z Y X : RingedSpace.{u, u}} (f : Y ⟶ X) (f' : Z ⟶ Y)
  {F : SheafOfModules.{u} (structureSheafRing X)} {A : GradedAlgebra.{u, u} (structureSheafRing X)}
  {ι : F ⟶ A.piece 1} {G : SheafOfModules.{u} (structureSheafRing Y)}
  {D : GradedAlgebra.{u, u} (structureSheafRing Y)} {ιD : G ⟶ D.piece 1}
  {E : GradedAlgebra.{u, u} (structureSheafRing Z)}
  (hA : IsExteriorAlgebra A ι) (hD : IsExteriorAlgebra D ιD)
  {c : (modulePullback f).obj F ⟶ G} {μ : (modulePullback f').obj G ⟶ E.piece 1}
  (hμ : SquareZero μ) (ε : modulePullback (f' ≫ f) ⟶ modulePullback f ⋙ modulePullback f')

/-- The comparison of Stacks 01CI is a cocycle. Let `A` be an exterior algebra of `F` on `X`,
let `D` be an exterior algebra of `G` on `Y`, and let `E` be any sheaf of graded algebras on `Z`.
A morphism `c : f^*F ⟶ G` makes `c ≫ ιD` a square-zero degree-one generator of `D`, and a
square-zero degree-one generator `μ` of `E` on `f'^*G` pulls back along `c` in the same way; so
all three comparisons of Stacks 01CI are defined, and the comparison of the composite
`f' ≫ f` is the composite of the two comparisons, read through any natural transformation
`ε : (f' ≫ f)^* ⟶ f'^* ∘ f^*` compatible with the pullback-adjunction units. -/
theorem pullbackComparison_comp
    (hε : ∀ (M : SheafOfModules.{u} (structureSheafRing X)) (U : (Opens X.carrier)ᵒᵖ)
      (x : M.val.obj U),
      (ε.app M).val.app ((opensMap (f' ≫ f)).op.obj U) (pullbackUnit (f' ≫ f) M U x) =
        pullbackUnit f' ((modulePullback f).obj M) ((opensMap f).op.obj U)
          (pullbackUnit f M U x))
    (n : ℤ) :
    pullbackComparison (f' ≫ f) hA (hμ.comp (ε.app F ≫ (modulePullback f').map c)) n =
      ε.app (A.piece n) ≫
        (modulePullback f').map (pullbackComparison f hA (hD.1.comp c) n) ≫
          pullbackComparison f' hD hμ n := by
  have key : ∀ (m : ℤ) (U : (Opens X.carrier)ᵒᵖ) (y : (A.piece m).val.obj U)
      (w : (D.piece m).val.obj ((opensMap f).op.obj U)),
      (pullbackComparison f hA (hD.1.comp c) m).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A.piece m) U y) = w →
      (ε.app (A.piece m) ≫ (modulePullback f').map (pullbackComparison f hA (hD.1.comp c) m) ≫
            pullbackComparison f' hD hμ m).val.app ((opensMap (f' ≫ f)).op.obj U)
          (pullbackUnit (f' ≫ f) (A.piece m) U y) =
        (pullbackComparison f' hD hμ m).val.app
            ((opensMap f').op.obj ((opensMap f).op.obj U))
          (pullbackUnit f' (D.piece m) ((opensMap f).op.obj U) w) := fun m U y w h => by
    subst h
    exact congrArg (fun z => (pullbackComparison f' hD hμ m).val.app
        ((opensMap f').op.obj ((opensMap f).op.obj U)) z)
      ((congrArg (fun z => ((modulePullback f').map
              (pullbackComparison f hA (hD.1.comp c) m)).val.app
            ((opensMap f').op.obj ((opensMap f).op.obj U)) z) (hε (A.piece m) U y)).trans
        (pullbackUnit_naturality f' (pullbackComparison f hA (hD.1.comp c) m)
          ((opensMap f).op.obj U) (pullbackUnit f (A.piece m) U y)))
  refine (pullbackComparison_unique (f' ≫ f) hA _
    (fun m => ε.app (A.piece m) ≫
      (modulePullback f').map (pullbackComparison f hA (hD.1.comp c) m) ≫
        pullbackComparison f' hD hμ m) (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n).symm
  · exact (key (i + j) U ((A.mul i j).app U a b) _
        (pullbackComparison_mul f hA (hD.1.comp c) i j U a b)).trans
      ((pullbackComparison_mul f' hD hμ i j ((opensMap f).op.obj U) _ _).trans
        (congrArg₂ (fun x y => (((E.mul i j).app
            ((opensMap f').op.obj ((opensMap f).op.obj U))) x) y)
          (key i U a _ rfl).symm (key j U b _ rfl).symm))
  · exact (key 0 U (A.one.eval U) _ (pullbackComparison_one f hA (hD.1.comp c) U)).trans
      (pullbackComparison_one f' hD hμ ((opensMap f).op.obj U))
  · refine (key 1 U (ι.val.app U s) _
        (pullbackComparison_generator f hA (hD.1.comp c) U s)).trans
      ((pullbackComparison_generator f' hD hμ ((opensMap f).op.obj U)
        (c.val.app ((opensMap f).op.obj U) (pullbackUnit f F U s))).trans ?_)
    exact congrArg (fun z => μ.val.app ((opensMap f').op.obj ((opensMap f).op.obj U)) z)
      ((pullbackUnit_naturality f' c ((opensMap f).op.obj U) (pullbackUnit f F U s)).symm.trans
        (congrArg (fun z => ((modulePullback f').map c).val.app
            ((opensMap f').op.obj ((opensMap f).op.obj U)) z) (hε F U s).symm))

end Composition

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Hom

open SheafOfModules.GradedAlgebra

variable {X' X S' S : Scheme.{u}}

/-- The canonical map on relative differential forms is the canonical comparison of Stacks 01CI
attached to the degree-one generator `f^*Ω_{X/S} ⟶ Ω^1_{X'/S'}` of the square, namely the
canonical map on relative differentials of Stacks 01UV followed by the degree-one generator of
`Ω^•_{X'/S'}`. -/
theorem relativeDifferentialFormsMap_eq_pullbackComparison (f : X' ⟶ X) (p : X ⟶ S)
    (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    relativeDifferentialFormsMap f p p' g hcomm n =
      pullbackComparison f.toLRSHom.toShHom
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
        ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
          (relativeDifferentials p')).1.comp (relativeDifferentialsMap f p p' g hcomm)) n :=
  (pullbackComparison_comp_unitalHom f.toLRSHom.toShHom
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        ((Scheme.Modules.pullback f).obj (relativeDifferentials p))).1
      (relativeDifferentialFormsComparison f p p' g hcomm) n).trans
    (pullbackComparison_congr f.toLRSHom.toShHom _
      (relativeDifferentialFormsComparison_generator f p p' g hcomm) _ _ n)

variable {X'' : Scheme.{u}} {S'' : Scheme.{u}}

/-- The canonical maps on relative differentials of two horizontally composable commuting
squares compose, as an equation of morphisms. The base morphism `g''` of the outer square is
arbitrary. -/
theorem relativeDifferentialsMap_pullbackComp (f : X' ⟶ X) (f' : X'' ⟶ X') (p : X ⟶ S)
    (p' : X' ⟶ S') (p'' : X'' ⟶ S'') (g : S' ⟶ S) (g' : S'' ⟶ S') (g'' : S'' ⟶ S)
    (hcomm : f ≫ p = p' ≫ g) (hcomm' : f' ≫ p' = p'' ≫ g')
    (hcomm'' : (f' ≫ f) ≫ p = p'' ≫ g'') :
    relativeDifferentialsMap (f' ≫ f) p p'' g'' hcomm'' =
      (Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullback f').map (relativeDifferentialsMap f p p' g hcomm) ≫
          relativeDifferentialsMap f' p' p'' g' hcomm' :=
  (((isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g hcomm).comp
    (isRelativeDifferentialsMap_relativeDifferentialsMap f' p' p'' g'
      hcomm')).eq_relativeDifferentialsMap g'' hcomm'').symm

/-- The canonical maps on relative differential forms of two horizontally composable commuting
squares compose, in every degree `n : ℤ`: the map `(f' ≫ f)^*Ω^n_{X/S} ⟶ Ω^n_{X''/S''}` of the
outer square is the coherence isomorphism `(f' ≫ f)^* ≅ f'^* ∘ f^*` of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, followed by `f'^*` of the map of the right-hand
square, followed by the map of the left-hand square. The three bases are arbitrary, as is the
base morphism `g''` of the outer square, and no hypothesis beyond commutativity is made on
either square. -/
theorem relativeDifferentialFormsMap_comp (f : X' ⟶ X) (f' : X'' ⟶ X') (p : X ⟶ S)
    (p' : X' ⟶ S') (p'' : X'' ⟶ S'') (g : S' ⟶ S) (g' : S'' ⟶ S') (g'' : S'' ⟶ S)
    (hcomm : f ≫ p = p' ≫ g) (hcomm' : f' ≫ p' = p'' ≫ g')
    (hcomm'' : (f' ≫ f) ≫ p = p'' ≫ g'') (n : ℤ) :
    relativeDifferentialFormsMap (f' ≫ f) p p'' g'' hcomm'' n =
      (Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentialForms p n) ≫
        (Scheme.Modules.pullback f').map (relativeDifferentialFormsMap f p p' g hcomm n) ≫
          relativeDifferentialFormsMap f' p' p'' g' hcomm' n := by
  have hκ : relativeDifferentialsMap (f' ≫ f) p p'' g'' hcomm'' ≫
        Scheme.Modules.exteriorGenerator (relativeDifferentials p'') =
      ((Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentials p) ≫
          (Scheme.Modules.pullback f').map (relativeDifferentialsMap f p p' g hcomm)) ≫
        (relativeDifferentialsMap f' p' p'' g' hcomm' ≫
          Scheme.Modules.exteriorGenerator (relativeDifferentials p'')) := by
    rw [(relativeDifferentialsMap_pullbackComp f f' p p' p'' g g' g'' hcomm hcomm'
      hcomm'').trans (Category.assoc _ _ _).symm]
    exact Category.assoc _ _ _
  refine (relativeDifferentialFormsMap_eq_pullbackComparison (f' ≫ f) p p'' g'' hcomm'' n).trans
    ((pullbackComparison_congr (f' ≫ f).toLRSHom.toShHom
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p)) hκ
          ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p'')).1.comp
            (relativeDifferentialsMap (f' ≫ f) p p'' g'' hcomm''))
          (((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
                (relativeDifferentials p'')).1.comp
              (relativeDifferentialsMap f' p' p'' g' hcomm')).comp
            ((Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentials p) ≫
              (Scheme.Modules.pullback f').map
                (relativeDifferentialsMap f p p' g hcomm))) n).trans
      ((pullbackComparison_comp f.toLRSHom.toShHom f'.toLRSHom.toShHom
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p'))
          ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p'')).1.comp
            (relativeDifferentialsMap f' p' p'' g' hcomm'))
          (Scheme.Modules.pullbackComp f' f).inv ?_ n).trans ?_))
  · intro M U x
    exact SheafOfModules.Hom.congr_val_app (pullbackComp_unit f' f M) U x
  · exact congrArg₂ (fun a b =>
      (Scheme.Modules.pullbackComp f' f).inv.app (relativeDifferentialForms p n) ≫
        (Scheme.Modules.pullback f').map a ≫ b)
      (relativeDifferentialFormsMap_eq_pullbackComparison f p p' g hcomm n).symm
      (relativeDifferentialFormsMap_eq_pullbackComparison f' p' p'' g' hcomm' n).symm

end AlgebraicGeometry.Scheme.Hom

end
