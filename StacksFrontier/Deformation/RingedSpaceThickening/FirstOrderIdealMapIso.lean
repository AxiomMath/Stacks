module

public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionIsomorphism

/-!
# The first-order ideal map is the pushed-forward conormal map

Let `D` be a morphism of first order thickenings of ringed spaces,

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

with ideals `ℐ` of `i` and `𝒥` of `t`. **Stacks 08KZ** attaches to it the canonical map
`f^* 𝒥 ⟶ ℐ` (`AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.firstOrderIdealMap`),
read on `X'` as a map out of `i_* f^* t^* 𝒥`. The same square, as a commutative square of
morphisms of ringed spaces, has the map of conormal sheaves `f^* 𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of
**Stacks 01R4** (`Stacks.ClosedImmersion.conormalSheafMap`). This file identifies the two: the
first-order ideal map, followed by the quotient map `ℐ ⟶ i_* i^* ℐ = i_* 𝒞_{X/X'}`, is the
pushforward along `i` of the conormal map. Since that quotient map is invertible for a first
order thickening, the first-order ideal map is invertible exactly when the conormal map is.

This is the bridge through which flatness enters the deformation problem of **Stacks 08U7** for
schemes: for a flat deformation the conormal map is invertible by flat base change
(**Stacks 0473**), so the ideal of the deformed space is identified with `f^* 𝒥` by the
canonical map, which is what makes a flat deformation a solution of the problem with `𝒢 = f^* 𝒥`
and `c` the identity (see `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.ofIsIso`).

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.idealMap_eq_idealSheafMap`: the
  canonical ideal map of **Stacks 08KZ** is the ideal sheaf map of the square.
* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.firstOrderIdealMap_comp_unit`:
  the first-order ideal map followed by the quotient map is the pushed-forward conormal map.
* `RingedSpaceThickening.MorphismOfThickenings.isIso_firstOrderIdealMap_of_isIso`:
  an invertible conormal map makes the first-order ideal map invertible.
* `AlgebraicGeometry.RingedSpaceThickening.kernel_comm_of_comm` and
  `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.ofComm`: for an invertible prescribed map,
  any morphism of deformed spaces under `X` and over `S'` is a morphism of solutions — the
  compatibility with the two identifications of the ideals is automatic, because both ideal
  inclusions are pinned down by `c` through the canonical map of Stacks 08KZ.
* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.isIso_conormalSheafMap_of_isIso`:
  the converse.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.isIso_firstOrderIdealMap`: the
  first-order ideal map of a solution with invertible prescribed map is invertible.
* `AlgebraicGeometry.RingedSpaceThickening.isIso_firstOrderIdealMap_of_iso`: invertibility of the
  first-order ideal map is invariant under isomorphism of thickenings under `X` and over `S'`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.ofIsIso`: a first order thickening
  over `t` whose first-order ideal map is invertible is a solution of **Stacks 08U7** for every
  invertible prescribed map `c`.

## References

* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The inclusion of an ideal sheaf is a monomorphism, being a kernel inclusion. -/
private theorem mono_idealSheafι {W W' : RingedSpace.{u, u}} (j : W ⟶ W') :
    Mono (Stacks.ClosedImmersion.idealSheafι j) :=
  inferInstanceAs (Mono (kernel.ι _))

namespace MorphismOfThickenings

variable (D : MorphismOfThickenings.{u})

/-- **The canonical ideal map of Stacks 08KZ is the ideal sheaf map of the square.** Both are
the factorisation through the ideal of `i` of the composite `(f')^* 𝒥 ⟶ (f')^* 𝒪_{S'} ⟶ 𝒪_{X'}`;
the inclusion of the ideal is a monomorphism. -/
theorem idealMap_eq_idealSheafMap :
    D.idealMap.1 = Stacks.ClosedImmersion.idealSheafMap D.comm := by
  have := mono_idealSheafι D.i
  rw [← cancel_mono (Stacks.ClosedImmersion.idealSheafι D.i),
    Stacks.ClosedImmersion.idealSheafMap_comp_ι]
  exact D.idealMap.2

/-- **The first-order ideal map, followed by the quotient map `ℐ ⟶ i_* i^* ℐ`, is the
pushed-forward conormal map**, up to an automorphism of `f^* t^* 𝒥`: precisely, it is the
pushforward along `i` of the conormal map of the square precomposed with the composite of the two
identifications of `i^* (f')^* 𝒥` with `f^* t^* 𝒥` used by **Stacks 08KZ** and by **Stacks 01R4**.

Both sides agree after the epimorphism `(f')^* 𝒥 ⟶ i_* f^* t^* 𝒥` of **Stacks 08KZ**: there the
left-hand side is the canonical ideal map followed by the quotient map, which by naturality of the
unit of `i^* ⊣ i_*` is the unit followed by `i_* i^*` of the ideal map. -/
theorem firstOrderIdealMap_comp_unit (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) :
    (D.firstOrderIdealMap hi ht).1 ≫
        (modulePullbackPushforwardAdjunction D.i).unit.app D.idealI =
      (modulePushforward D.i).map
        ((D.reducedPullbackComparison.inv ≫
          (Stacks.ClosedImmersion.pullbackCompIso D.comm D.idealJ).inv) ≫
          Stacks.ClosedImmersion.conormalSheafMap D.comm) := by
  have : Epi (D.firstOrderSurjection hi ht) := D.firstOrderSurjection_epi hi ht
  rw [← cancel_epi (D.firstOrderSurjection hi ht), ← Category.assoc,
    (D.firstOrderIdealMap hi ht).2.1, idealMap_eq_idealSheafMap,
    ← (modulePullbackPushforwardAdjunction D.i).unit_naturality]
  simp only [firstOrderSurjection, Stacks.ClosedImmersion.conormalSheafMap,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **An invertible conormal map makes the first-order ideal map invertible.** By
`firstOrderIdealMap_comp_unit`, the first-order ideal map followed by the quotient map, which is
invertible for a first order thickening, is the pushforward of an invertible map. -/
theorem isIso_firstOrderIdealMap_of_isIso (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t)
    [IsIso (Stacks.ClosedImmersion.conormalSheafMap D.comm)] :
    IsIso (D.firstOrderIdealMap hi ht).1 := by
  have := isIso_unit_app_idealSheaf D.i hi
  have h : IsIso ((D.firstOrderIdealMap hi ht).1 ≫
      (modulePullbackPushforwardAdjunction D.i).unit.app D.idealI) := by
    rw [firstOrderIdealMap_comp_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((modulePullbackPushforwardAdjunction D.i).unit.app D.idealI)

/-- **The converse: an invertible first-order ideal map makes the conormal map invertible.**
By `firstOrderIdealMap_comp_unit`, the pushforward along `i` of the conormal map, precomposed with
an isomorphism, is a composite of isomorphisms; the pushforward along a thickening is fully
faithful, so it reflects isomorphisms. -/
theorem isIso_conormalSheafMap_of_isIso (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) [IsIso (D.firstOrderIdealMap hi ht).1] :
    IsIso (Stacks.ClosedImmersion.conormalSheafMap D.comm) := by
  have := isIso_unit_app_idealSheaf D.i hi
  have : (modulePushforward D.i).Full :=
    (closedQuotientOfIsThickening D.i hi.1).full_modulePushforward
  have : (modulePushforward D.i).Faithful :=
    (closedQuotientOfIsThickening D.i hi.1).faithful_modulePushforward
  have : IsIso ((modulePushforward D.i).map
      ((D.reducedPullbackComparison.inv ≫
        (Stacks.ClosedImmersion.pullbackCompIso D.comm D.idealJ).inv) ≫
        Stacks.ClosedImmersion.conormalSheafMap D.comm)) := by
    rw [← firstOrderIdealMap_comp_unit D hi ht]
    infer_instance
  have : IsIso ((D.reducedPullbackComparison.inv ≫
        (Stacks.ClosedImmersion.pullbackCompIso D.comm D.idealJ).inv) ≫
        Stacks.ClosedImmersion.conormalSheafMap D.comm) :=
    isIso_of_reflects_iso _ (modulePushforward D.i)
  exact IsIso.of_isIso_comp_left (D.reducedPullbackComparison.inv ≫
    (Stacks.ClosedImmersion.pullbackCompIso D.comm D.idealJ).inv) _

end MorphismOfThickenings

/-! ### Solutions from an invertible first-order ideal map -/

section OfIsIso

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-- The morphism of thickenings of a first order thickening `i : X ⟶ X'` over `t`. -/
abbrev thickeningSquare {X' : RingedSpace.{u, u}} (i : X ⟶ X') (f' : X' ⟶ S')
    (hi : IsFirstOrderThickening i) (comm : i ≫ f' = f ≫ t) : MorphismOfThickenings.{u} :=
  { X := X, X' := X', S := S, S' := S', i := i, t := t, f := f, f' := f',
    i_isThickening := hi.1, t_isThickening := ht.1, comm := comm }

/-- **A first order thickening over `t` whose first-order ideal map is invertible is a solution
of the deformation problem of Stacks 08U7, for every invertible prescribed map `c`.** The ideal
of the thickening is identified with `𝒢` by the inverse of the first-order ideal map followed by
the pushforward of `c`, and the compatibility equation of Stacks 08U7 then holds by
construction. -/
noncomputable def DeformationSolution.ofIsIso {X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (f' : X' ⟶ S') (hi : IsFirstOrderThickening i) (comm : i ≫ f' = f ≫ t)
    [hD : IsIso ((thickeningSquare ht i f' hi comm).firstOrderIdealMap hi ht).1] [IsIso c] :
    DeformationSolution t ht f G c where
  X' := X'
  i := i
  f' := f'
  i_firstOrder := hi
  comm := comm
  kernelIso := (asIso ((thickeningSquare ht i f' hi comm).firstOrderIdealMap hi ht).1).symm ≪≫
    (modulePushforward i).mapIso (asIso c)
  compatibility := by
    intro D
    exact IsIso.hom_inv_id_assoc _ _

end OfIsIso

/-! ### Morphisms of solutions are determined by their underlying morphism -/

section Hom

/-- Transposing along the composite adjunction `(a ≫ b)^* ⊣ a_* ⋙ b_*` a map precomposed with the
comparison `b^* ⋙ a^* ≅ (a ≫ b)^*` is transposing along the adjunction of the composite. -/
theorem homEquiv_compUniq_inv {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (N : SheafOfModules.{u} (structureSheafRing Z)) (Mx : SheafOfModules.{u} (structureSheafRing X))
    (φ : (modulePullback (a ≫ b)).obj N ⟶ Mx) :
    ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction a)).homEquiv
        _ _ ((modulePullbackCompUniq a b).inv.app N ≫ φ) =
      (modulePullbackPushforwardAdjunction (a ≫ b)).homEquiv _ _ φ := by
  let adj1 := modulePullbackPushforwardAdjunction (a ≫ b)
  let adj2 := ((modulePullbackPushforwardAdjunction b).comp
    (modulePullbackPushforwardAdjunction a)).ofNatIsoRight (modulePushforwardCompSymm a b).symm
  have hCU : modulePullbackCompUniq a b = Adjunction.leftAdjointUniq adj1 adj2 := rfl
  have h1 : adj1.homEquiv _ _ φ =
      adj2.homEquiv _ _ ((modulePullbackCompUniq a b).inv.app N ≫ φ) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    conv_lhs => rw [← Iso.hom_inv_id_app_assoc (modulePullbackCompUniq a b) N φ]
    rw [Functor.map_comp, ← Category.assoc, hCU, Adjunction.unit_leftAdjointUniq_hom_app]
  rw [h1, Adjunction.homEquiv_ofNatIsoRight_apply]
  rfl

/-- Transposition along the pullback-pushforward adjunction is compatible with transport along an
equality of morphisms of ringed spaces. -/
theorem homEquiv_eqToHom_comp {X Y : RingedSpace.{u, u}} {p q : X ⟶ Y} (e : p = q)
    (N : SheafOfModules.{u} (structureSheafRing Y)) (Mx : SheafOfModules.{u} (structureSheafRing X))
    (ψ : (modulePullback q).obj N ⟶ Mx) :
    (modulePullbackPushforwardAdjunction p).homEquiv _ _
        (eqToHom (congrArg (fun g => (modulePullback g).obj N) e) ≫ ψ) =
      (modulePullbackPushforwardAdjunction q).homEquiv _ _ ψ ≫
        eqToHom (congrArg (fun g => (modulePushforward g).obj Mx) e.symm) := by
  subst e
  simp

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

namespace DeformationSolution

/-- The map `𝒥 ⟶ (f ≫ t)_* 𝒢` attached to the prescribed map `c`. -/
noncomputable def baseIdealMap (t : S ⟶ S') (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) :
    AlgebraicGeometry.SheafOfModules.idealSheaf t ⟶ (modulePushforward (f ≫ t)).obj G :=
  (modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
    ((modulePullbackCompUniq f t).hom.app _ ≫ c)

end DeformationSolution

/-- **The reduction map of Stacks 08KZ followed by `i_* c`, read on the base**: its transpose along
`f'` is the transpose `𝒥 ⟶ (f ≫ t)_* 𝒢` of `c`, so it depends only on `f`, `t` and `c`. -/
theorem MorphismOfThickenings.homEquiv_firstOrderSurjection (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    {G : SheafOfModules.{u} (structureSheafRing D.X)}
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ G) :
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
        (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c) =
      DeformationSolution.baseIdealMap D.t D.f G c ≫
        eqToHom (congrArg (fun g => (modulePushforward g).obj G) D.comm.symm) := by
  have h : D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c =
      (modulePullbackPushforwardAdjunction D.i).homEquiv _ _
        (D.reducedPullbackComparison.hom ≫ c) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, MorphismOfThickenings.firstOrderSurjection,
      Category.assoc]
  have hcomp : ∀ y : (modulePullback D.i).obj ((modulePullback D.f').obj D.idealJ) ⟶ G,
      (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
          ((modulePullbackPushforwardAdjunction D.i).homEquiv _ _ y) =
        ((modulePullbackPushforwardAdjunction D.f').comp
          (modulePullbackPushforwardAdjunction D.i)).homEquiv _ _ y := by
    intro y
    rw [Adjunction.comp_homEquiv]
    rfl
  have hr : D.reducedPullbackComparison.hom ≫ c =
      (modulePullbackCompUniq D.i D.f').inv.app D.idealJ ≫
        (eqToHom (congrArg (fun h : D.X ⟶ D.S' => (modulePullback h).obj D.idealJ) D.comm) ≫
          (modulePullbackCompUniq D.f D.t).hom.app D.idealJ ≫ c) := by
    simp only [MorphismOfThickenings.reducedPullbackComparison, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, eqToIso.hom, Category.assoc]
  rw [h, hcomp, hr, homEquiv_compUniq_inv]
  exact homEquiv_eqToHom_comp D.comm _ _ _

/-- If `x` after the reduction map of Stacks 08KZ and `i_* c` is `(f')^♯` restricted to the
pulled-back ideal, then read on the base that restriction is the map attached to `c` followed by
`f'_* x`. -/
private theorem idealSheafι_comp_structureSheafModuleHom_of_ambient (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    {G : SheafOfModules.{u} (structureSheafRing D.X)}
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ G)
    (x : (modulePushforward D.i).obj G ⟶ SheafOfModules.unit (structureSheafRing D.X'))
    (h : D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c ≫ x = D.ambientIdealMap) :
    Stacks.ClosedImmersion.idealSheafι D.t ≫ structureSheafModuleHom D.f' =
      DeformationSolution.baseIdealMap D.t D.f G c ≫
        eqToHom (congrArg (fun g => (modulePushforward g).obj G) D.comm.symm) ≫
          (modulePushforward D.f').map x := by
  have e := congrArg ((modulePullbackPushforwardAdjunction D.f').homEquiv _ _) h
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    D.homEquiv_firstOrderSurjection hi ht c] at e
  exact (homEquiv_map_comp_pullbackUnitToUnit D.f' _ _).symm.trans
    (e.symm.trans (Category.assoc _ _ _))

namespace DeformationSolution

/-- The morphism of thickenings underlying a solution, as a reducible structure literal. -/
abbrev square (Q : DeformationSolution t ht f G c) : MorphismOfThickenings.{u} :=
  { X := X, X' := Q.X', S := S, S' := S', i := Q.i, t := t, f := f, f' := Q.f',
    i_isThickening := Q.i_firstOrder.1, t_isThickening := ht.1, comm := Q.comm }

/-- The ideal inclusion of a solution, after the canonical reduction map of Stacks 08KZ and the
prescribed map, is the restriction of `(f')^♯` to the pulled-back ideal. -/
theorem firstOrderSurjection_comp_idealInclusion (Q : DeformationSolution t ht f G c) :
    Q.square.firstOrderSurjection Q.i_firstOrder ht ≫
        (modulePushforward Q.i).map c ≫ Q.idealInclusion =
      Q.square.ambientIdealMap := by
  let D := Q.square
  let g := (D.firstOrderIdealMap Q.i_firstOrder ht).1
  have hc : g ≫ Q.kernelIso.hom = (modulePushforward Q.i).map c := Q.compatibility
  have hc' : (modulePushforward Q.i).map c ≫ Q.kernelIso.inv = g := by
    rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : D.firstOrderSurjection Q.i_firstOrder ht ≫ g = D.idealMap.1 :=
    (D.firstOrderIdealMap Q.i_firstOrder ht).2.1
  have h2 : D.idealMap.1 ≫ kernel.ι Q.structureMap = D.ambientIdealMap := D.idealMap.2
  have e1 : (modulePushforward Q.i).map c ≫ (Q.kernelIso.inv ≫ kernel.ι Q.structureMap) =
      g ≫ kernel.ι Q.structureMap :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ kernel.ι Q.structureMap) hc')
  have e2 : D.firstOrderSurjection Q.i_firstOrder ht ≫ g ≫ kernel.ι Q.structureMap =
      D.ambientIdealMap :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ kernel.ι Q.structureMap) h1).trans h2)
  exact (congrArg (D.firstOrderSurjection Q.i_firstOrder ht ≫ ·) e1).trans e2

/-- The transpose along `f'` of the composite of the reduction map of Stacks 08KZ, the
prescribed map and the ideal inclusion of a solution. -/
theorem homEquiv_ambientIdealMap (Q : DeformationSolution t ht f G c) :
    (modulePullbackPushforwardAdjunction Q.f').homEquiv _ _
        Q.square.ambientIdealMap =
      Stacks.ClosedImmersion.idealSheafι t ≫ structureSheafModuleHom Q.f' :=
  homEquiv_map_comp_pullbackUnitToUnit Q.f' _ _

/-- The transpose along `f'` of a map out of `i_* 𝒢` precomposed with the reduction map of
Stacks 08KZ and the prescribed map. -/
theorem homEquiv_firstOrderSurjection_comp (Q : DeformationSolution t ht f G c)
    {Y : SheafOfModules.{u} (structureSheafRing Q.X')} (x : (modulePushforward Q.i).obj G ⟶ Y) :
    (modulePullbackPushforwardAdjunction Q.f').homEquiv _ _
        ((Q.square.firstOrderSurjection Q.i_firstOrder ht ≫
          (modulePushforward Q.i).map c) ≫ x) =
      baseIdealMap t f G c ≫
        eqToHom (congrArg (fun g => (modulePushforward g).obj G) Q.comm.symm) ≫
          (modulePushforward Q.f').map x := by
  rw [Adjunction.homEquiv_naturality_right,
    Q.square.homEquiv_firstOrderSurjection Q.i_firstOrder ht c]
  exact Category.assoc _ _ _

/-- **The ideal inclusion of a solution is determined by the prescribed map**: read on the base,
the restriction of `(f')^♯` to `𝒥` is the map `𝒥 ⟶ (f ≫ t)_* 𝒢` attached to `c` followed by the
ideal inclusion. -/
theorem idealSheafι_comp_structureSheafModuleHom (Q : DeformationSolution t ht f G c) :
    Stacks.ClosedImmersion.idealSheafι t ≫ structureSheafModuleHom Q.f' =
      baseIdealMap t f G c ≫
        eqToHom (congrArg (fun g => (modulePushforward g).obj G) Q.comm.symm) ≫
          (modulePushforward Q.f').map Q.idealInclusion := by
  exact idealSheafι_comp_structureSheafModuleHom_of_ambient Q.square Q.i_firstOrder ht c _
    Q.firstOrderSurjection_comp_idealInclusion

end DeformationSolution

/-- **A morphism of deformed spaces under `X` and over `S'` between two solutions is the identity
on the prescribed ideal**, as soon as the prescribed map `c` is invertible. -/
theorem kernel_comm_of_comm [IsIso c] (Q₁ Q₂ : DeformationSolution t ht f G c)
    (h : Q₁.X' ⟶ Q₂.X') (th : Q₁.i ≫ h = Q₂.i) (bh : h ≫ Q₂.f' = Q₁.f') :
    Q₂.idealInclusion ≫ structureSheafModuleHom h =
      (pushforwardIsoOfComp Q₁.i h Q₂.i th).hom.app G ≫
        (modulePushforward h).map Q₁.idealInclusion := by
  have hfos := Q₂.square.firstOrderSurjection_epi Q₂.i_firstOrder ht
  refine (cancel_epi (Q₂.square.firstOrderSurjection Q₂.i_firstOrder ht ≫
      (modulePushforward Q₂.i).map c)).1 ?_
  refine ((modulePullbackPushforwardAdjunction Q₂.f').homEquiv _ _).injective ?_
  rw [Q₂.homEquiv_firstOrderSurjection_comp, Q₂.homEquiv_firstOrderSurjection_comp]
  have e₂ := Q₂.idealSheafι_comp_structureSheafModuleHom
  have e₁ := Q₁.idealSheafι_comp_structureSheafModuleHom
  obtain ⟨X'₁, i₁, f'₁, hi₁, comm₁, kI₁, compat₁⟩ := Q₁
  obtain ⟨X'₂, i₂, f'₂, hi₂, comm₂, kI₂, compat₂⟩ := Q₂
  dsimp only at h th bh e₁ e₂ ⊢
  subst th bh
  refine (?_ : _ = Stacks.ClosedImmersion.idealSheafι t ≫
    structureSheafModuleHom (h ≫ f'₂)).trans ?_
  · exact (congrArg (· ≫ (modulePushforward f'₂).map (structureSheafModuleHom h)) e₂).symm
  · exact e₁.trans rfl

/-- **The first-order ideal map of a solution is invertible when the prescribed map is**: by the
compatibility equation of Stacks 08U7 it is `i_* c` followed by the inverse of the
identification of the ideal with `𝒢`. -/
theorem DeformationSolution.isIso_firstOrderIdealMap [IsIso c]
    (Q : DeformationSolution t ht f G c) :
    IsIso (Q.square.firstOrderIdealMap Q.i_firstOrder ht).1 := by
  have hc : (Q.square.firstOrderIdealMap Q.i_firstOrder ht).1 ≫ Q.kernelIso.hom =
      (modulePushforward Q.i).map c := Q.compatibility
  have : IsIso ((Q.square.firstOrderIdealMap Q.i_firstOrder ht).1 ≫ Q.kernelIso.hom) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ Q.kernelIso.hom

/-- **A morphism of deformed spaces under `X` and over `S'` is a morphism of solutions**, when the
prescribed map `c` is invertible: its compatibility with the identifications of the two ideals
with `𝒢` is automatic (`kernel_comm_of_comm`). -/
noncomputable def SolutionHom.ofComm [IsIso c] {Q₁ Q₂ : DeformationSolution t ht f G c}
    (h : Q₁.X' ⟶ Q₂.X') (th : Q₁.i ≫ h = Q₂.i) (bh : h ≫ Q₂.f' = Q₁.f') :
    SolutionHom Q₁ Q₂ where
  hom := h
  thickening_comm := th
  base_comm := bh
  kernel_comm := kernel_comm_of_comm Q₁ Q₂ h th bh

/-- Two solutions with invertible prescribed map are isomorphic as soon as their deformed spaces
are related by a morphism under `X` and over `S'`. -/
theorem isomorphic_of_comm [IsIso c] {Q₁ Q₂ : DeformationSolution t ht f G c}
    (h : Q₁.X' ⟶ Q₂.X') (th : Q₁.i ≫ h = Q₂.i) (bh : h ≫ Q₂.f' = Q₁.f') : Isomorphic Q₁ Q₂ :=
  (isomorphic_iff_nonempty_solutionHom Q₁ Q₂).2 ⟨SolutionHom.ofComm h th bh⟩

/-- The structure-sheaf map of an endomorphism equal to the identity is invertible. -/
theorem isIso_structureSheafModuleHom_of_eq_id {Y : RingedSpace.{u, u}} (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) : IsIso (structureSheafModuleHom g) := by
  subst hg
  have : structureSheafModuleHom (𝟙 Y) =
      (modulePushforwardId Y).inv.app (SheafOfModules.unit (structureSheafRing Y)) := by
    ext U
    rfl
  rw [this]
  infer_instance

/-- The structure-sheaf map of an isomorphism of ringed spaces is a monomorphism. -/
theorem mono_structureSheafModuleHom {Y Z : RingedSpace.{u, u}} (h : Y ⟶ Z) [IsIso h] :
    Mono (structureSheafModuleHom h) := by
  have : IsIso (structureSheafModuleHom h ≫ (modulePushforward h).map
      (structureSheafModuleHom (inv h))) :=
    isIso_structureSheafModuleHom_of_eq_id (inv h ≫ h) (IsIso.inv_hom_id h)
  exact mono_of_mono (structureSheafModuleHom h)
    ((modulePushforward h).map (structureSheafModuleHom (inv h)))

/-- **Maps out of the transported pulled-back ideal agreeing with `(f')^♯` are natural.** For two
first order thickenings `i₁ : X ⟶ X'₁` and `i₁ ≫ h : X ⟶ X'₂` over `t`, with `h` over `S'`, let
`γⱼ` be maps out of the transported pulled-back ideal which after the reduction map of
Stacks 08KZ are the restriction of `(f'ⱼ)^♯` to the pulled-back ideal. Then `γ₂ ≫ h^♯` is the
pushforward along `h` of `γ₁`. -/
theorem comp_structureSheafModuleHom_eq_of_ambient {X'₁ X'₂ : RingedSpace.{u, u}} (i₁ : X ⟶ X'₁)
    (hi₁ : IsFirstOrderThickening i₁) (f'₂ : X'₂ ⟶ S') (h : X'₁ ⟶ X'₂)
    (comm₁ : i₁ ≫ (h ≫ f'₂) = f ≫ t) (hi₂ : IsFirstOrderThickening (i₁ ≫ h))
    (comm₂ : (i₁ ≫ h) ≫ f'₂ = f ≫ t)
    (γ₁ : (modulePushforward i₁).obj
      ((modulePullback f).obj ((modulePullback t).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t))) ⟶
        SheafOfModules.unit (structureSheafRing X'₁))
    (hγ₁ : (thickeningSquare ht i₁ (h ≫ f'₂) hi₁ comm₁).firstOrderSurjection hi₁ ht ≫ γ₁ =
      (thickeningSquare ht i₁ (h ≫ f'₂) hi₁ comm₁).ambientIdealMap)
    (γ₂ : (modulePushforward (i₁ ≫ h)).obj
      ((modulePullback f).obj ((modulePullback t).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t))) ⟶
        SheafOfModules.unit (structureSheafRing X'₂))
    (hγ₂ : (thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).firstOrderSurjection hi₂ ht ≫ γ₂ =
      (thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).ambientIdealMap) :
    γ₂ ≫ structureSheafModuleHom h =
      (pushforwardIsoOfComp i₁ h (i₁ ≫ h) rfl).hom.app _ ≫ (modulePushforward h).map γ₁ := by
  have hfos := (thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).firstOrderSurjection_epi hi₂ ht
  have e₁ := idealSheafι_comp_structureSheafModuleHom_of_ambient
    (thickeningSquare ht i₁ (h ≫ f'₂) hi₁ comm₁) hi₁ ht (𝟙 _) γ₁ (by simpa using hγ₁)
  have a₂ : (modulePullbackPushforwardAdjunction f'₂).homEquiv _ _
      (thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).ambientIdealMap =
      Stacks.ClosedImmersion.idealSheafι t ≫ structureSheafModuleHom f'₂ :=
    homEquiv_map_comp_pullbackUnitToUnit _ _ _
  have b₂ := (thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).homEquiv_firstOrderSurjection hi₂ ht
    (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at b₂
  refine (cancel_epi ((thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).firstOrderSurjection hi₂
    ht)).1 ?_
  refine ((modulePullbackPushforwardAdjunction f'₂).homEquiv _ _).injective ?_
  rw [← Category.assoc, hγ₂, Adjunction.homEquiv_naturality_right, a₂,
    Adjunction.homEquiv_naturality_right, b₂]
  exact e₁.trans rfl

/-- The first-order ideal map followed by the ideal inclusion is, after the reduction map of
Stacks 08KZ, the restriction of `(f')^♯` to the pulled-back ideal. -/
theorem firstOrderSurjection_comp_firstOrderIdealMap_comp {X' : RingedSpace.{u, u}} (i : X ⟶ X')
    (f' : X' ⟶ S') (hi : IsFirstOrderThickening i) (comm : i ≫ f' = f ≫ t) :
    (thickeningSquare ht i f' hi comm).firstOrderSurjection hi ht ≫
        ((thickeningSquare ht i f' hi comm).firstOrderIdealMap hi ht).1 ≫
          Stacks.ClosedImmersion.idealSheafι i =
      (thickeningSquare ht i f' hi comm).ambientIdealMap :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) ((thickeningSquare ht i f' hi comm).firstOrderIdealMap hi ht).2.1).trans
      (thickeningSquare ht i f' hi comm).idealMap.2)

/-- **The first-order ideal map is invariant under isomorphism of thickenings**: if `h` is an
isomorphism under `X` and over `S'` and the first-order ideal map of the source is invertible, so
is that of the target. -/
theorem isIso_firstOrderIdealMap_of_iso {X'₁ X'₂ : RingedSpace.{u, u}} (i₁ : X ⟶ X'₁)
    (f'₁ : X'₁ ⟶ S') (hi₁ : IsFirstOrderThickening i₁) (comm₁ : i₁ ≫ f'₁ = f ≫ t)
    (i₂ : X ⟶ X'₂) (f'₂ : X'₂ ⟶ S') (hi₂ : IsFirstOrderThickening i₂)
    (comm₂ : i₂ ≫ f'₂ = f ≫ t) (h : X'₁ ⟶ X'₂) [IsIso h] (th : i₁ ≫ h = i₂)
    (bh : h ≫ f'₂ = f'₁)
    [IsIso ((thickeningSquare ht i₁ f'₁ hi₁ comm₁).firstOrderIdealMap hi₁ ht).1] :
    IsIso ((thickeningSquare ht i₂ f'₂ hi₂ comm₂).firstOrderIdealMap hi₂ ht).1 := by
  subst th bh
  set F₁ := ((thickeningSquare ht i₁ (h ≫ f'₂) hi₁ comm₁).firstOrderIdealMap hi₁ ht).1
  set F₂ := ((thickeningSquare ht (i₁ ≫ h) f'₂ hi₂ comm₂).firstOrderIdealMap hi₂ ht).1
  have nat := comp_structureSheafModuleHom_eq_of_ambient (ht := ht) i₁ hi₁ f'₂ h comm₁ hi₂ comm₂
    (F₁ ≫ Stacks.ClosedImmersion.idealSheafι i₁)
    (firstOrderSurjection_comp_firstOrderIdealMap_comp (ht := ht) i₁ (h ≫ f'₂) hi₁ comm₁)
    (F₂ ≫ Stacks.ClosedImmersion.idealSheafι (i₁ ≫ h))
    (firstOrderSurjection_comp_firstOrderIdealMap_comp (ht := ht) (i₁ ≫ h) f'₂ hi₂ comm₂)
  have hra : (modulePushforward h).IsRightAdjoint := modulePushforward_isRightAdjoint h
  have := mono_idealSheafι i₁
  have hmono₁ : Mono ((modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁)) :=
    Functor.map_mono _ _
  have w : (Stacks.ClosedImmersion.idealSheafι (i₁ ≫ h) ≫ structureSheafModuleHom h) ≫
      (modulePushforward h).map (structureSheafModuleHom i₁) = 0 :=
    (Category.assoc _ _ _).trans (kernel.condition _)
  let κ := kernel.lift _ _ w ≫
    inv (kernelComparison (structureSheafModuleHom i₁) (modulePushforward h))
  have h1 : inv (kernelComparison (structureSheafModuleHom i₁) (modulePushforward h)) ≫
      (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁) =
      kernel.ι ((modulePushforward h).map (structureSheafModuleHom i₁)) := by
    rw [IsIso.inv_comp_eq, kernelComparison_comp_ι]
  have hκ : κ ≫ (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁) =
      Stacks.ClosedImmersion.idealSheafι (i₁ ≫ h) ≫ structureSheafModuleHom h := by
    rw [Category.assoc, h1, kernel.lift_ι]
  let M := (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t))
  have e1 : (F₂ ≫ κ) ≫ (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁) =
      F₂ ≫ (Stacks.ClosedImmersion.idealSheafι (i₁ ≫ h) ≫ structureSheafModuleHom h) := by
    rw [Category.assoc, hκ]
  have e2 : F₂ ≫ (Stacks.ClosedImmersion.idealSheafι (i₁ ≫ h) ≫ structureSheafModuleHom h) =
      ((pushforwardIsoOfComp i₁ h (i₁ ≫ h) rfl).hom.app M ≫ (modulePushforward h).map F₁) ≫
        (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁) := by
    refine ((Category.assoc _ _ _).symm.trans nat).trans ?_
    rw [Functor.map_comp, Category.assoc]
  have hfac := (cancel_mono _).1 (e1.trans e2)
  have hiso : IsIso (F₂ ≫ κ) := by
    rw [hfac]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      ((pushforwardIsoOfComp i₁ h (i₁ ≫ h) rfl).app M).isIso_hom (Functor.map_isIso _ _)
  have := mono_idealSheafι (i₁ ≫ h)
  have := mono_structureSheafModuleHom h
  have hmκ : Mono κ := by
    have : Mono (κ ≫ (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁)) := by
      rw [hκ]
      exact mono_comp _ _
    exact mono_of_mono _ ((modulePushforward h).map (Stacks.ClosedImmersion.idealSheafι i₁))
  have hκiso : IsIso κ := by
    have : IsSplitEpi κ := ⟨⟨⟨inv (F₂ ≫ κ) ≫ F₂, by simp⟩⟩⟩
    exact isIso_of_mono_of_epi κ
  exact IsIso.of_isIso_comp_right F₂ κ

end Hom

end AlgebraicGeometry.RingedSpaceThickening

