module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBundle.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Scheme

/-!
# Base change of a projective bundle

Let `g : X ⟶ Y` be a morphism of schemes, `E` a quasi-coherent sheaf of modules on `Y` and `E'`
a quasi-coherent sheaf of modules on `X` identified with `g^*E`. This file proves that

```
𝐏(E')  ⟶  𝐏(E)
  |          |
  v          v
  X    ⟶     Y
```

is cartesian: the projective bundle of a pullback *is* the base change of the projective bundle.

The two inputs are
`Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange` — the base change of a relative
`Proj` along a morphism of base schemes, given an identification of the graded algebras — and
`Stacks.RelativeProj.symmetricSituationPullbackPieceIso`, Stacks tag 01CI for the symmetric
algebra, which supplies that identification degreewise. What this file adds is the assembly of
the latter into the *unital homomorphism of sheaves of graded algebras* that the former consumes.

## Main definitions

* `Stacks.RelativeProj.symmetricSituationPullbackHom`: the identification
  `g^*Sym(E) ⟶ Sym(E')` as a `SheafOfModules.GradedAlgebra.UnitalHom`.
* `Stacks.RelativeProj.projectiveBundleBaseChange`: the comparison morphism `𝐏(E') ⟶ 𝐏(E)`.
* `Stacks.RelativeProj.projectiveBundleBaseChangeIso`: the comparison with the fibre product,
  `𝐏(E') ≅ 𝐏(E) ×_Y X`.
* `Stacks.RelativeProj.projectiveBundleBaseChangeIsoFlip`: the same comparison written over the
  other fibre product, `𝐏(E') ≅ X ×_Y 𝐏(E)`.

## Main results

* `Stacks.RelativeProj.isPullback_projectiveBundleBaseChange`: **the square above is
  cartesian.**
* `Stacks.RelativeProj.projectiveBundleBaseChangeIso_hom_fst` and `_hom_snd`: the comparison
  isomorphism sits over `𝐏(E)` and over `X`.
* `Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange` and
  `Stacks.RelativeProj.projectiveBundleBaseChangeIsoFlip_hom_fst` and `_hom_snd`: the same
  square and the same two equations for `pullback g (projectiveBundleToBase Y E)`.

## Why both orientations of the fibre product

`pullback f h` and `pullback h f` are different objects — canonically isomorphic, but not the
same term — so a comparison isomorphism with one of them does not typecheck against the other.
The two are therefore both stated, each from the corresponding orientation of the one cartesian
square by `CategoryTheory.IsPullback.flip`; nothing but `IsPullback.isoPullback_hom_fst` and
`_hom_snd` is involved. Which orientation a consumer needs is fixed by *which* projection it
wants to name: a statement that pins the comparison down by its projection to the new base
needs `pullback.fst g π`, and so needs `projectiveBundleBaseChangeIsoFlip`.

## Implementation notes

The three fields of the unital homomorphism are available without any new mathematics. The
degreewise components are the isomorphisms of
`Stacks.RelativeProj.symmetricSituationPullbackPieceIso`, and no transport is needed because
`Stacks.Conormal.gradedPullback_piece` holds by `rfl` and
`Stacks.RelativeProj.symmetricSituation_algebra` identifies the algebra of the symmetric
situation with `SheafOfModules.sheafifiedSymmetricAlgebra`, also by `rfl`. Multiplicativity and
the unit law are `Stacks.RingedSpace.pullbackSymmetricPieceIso_mul` and `_one`, which are stated
for arbitrary homogeneous local sections over an arbitrary open and so are exactly the two
fields, not a weaker sectionwise form.

**The two situations must be supplied by name.** Written as
`Situation.isPullback_relativeProjBaseChange g Φ hΦ`, leaving `s` and `s'` to be inferred from
`g : X ⟶ Y`, elaboration dies at `isDefEq` on the 200000-heartbeat budget: the unifier is asked
to solve `?s'.base ≡ X` with `?s'` still a metavariable. Passing
`(s := symmetricSituationOfQuasicoherent Y E)` and
`(s' := symmetricSituationOfQuasicoherent X E')` removes the whole cost. The statement itself is
cheap in either spelling.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- The identification of the graded algebra of the projective-bundle situation of `E'` with the
pullback along `g` of that of `E`, as a unital homomorphism of sheaves of graded algebras. This
is the datum `Stacks.RelativeProj.Situation.isPullback_relativeProjBaseChange` consumes. -/
public def symmetricSituationPullbackHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback g (symmetricSituationOfQuasicoherent Y E).algebra)
      (symmetricSituationOfQuasicoherent X E').algebra where
  app n := (symmetricSituationPullbackPieceIso g E E' hE n).hom
  map_mul i j U x y :=
    Stacks.RingedSpace.pullbackSymmetricPieceIso_mul g.toLRSHom.toShHom
      (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥Y) E)
      (SheafOfModules.GradedAlgebra.isSymmetricAlgebra_ofIso hE.symm
        (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
          (Opens.grothendieckTopology ↥X) E')) i j U x y
  map_one U :=
    Stacks.RingedSpace.pullbackSymmetricPieceIso_one g.toLRSHom.toShHom
      (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥Y) E)
      (SheafOfModules.GradedAlgebra.isSymmetricAlgebra_ofIso hE.symm
        (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
          (Opens.grothendieckTopology ↥X) E')) U

/-- The identification of graded algebras is an isomorphism in every degree. -/
public instance isIso_symmetricSituationPullbackHom_app (n : ℤ) :
    IsIso ((symmetricSituationPullbackHom g E E' hE).app n) :=
  (symmetricSituationPullbackPieceIso g E E' hE n).isIso_hom

/-- **The base-change comparison morphism of projective bundles**, `𝐏(E') ⟶ 𝐏(E)`. -/
public def projectiveBundleBaseChange : projectiveBundle X E' ⟶ projectiveBundle Y E :=
  Situation.relativeProjBaseChange
    (s := symmetricSituationOfQuasicoherent Y E) (s' := symmetricSituationOfQuasicoherent X E')
    g (symmetricSituationPullbackHom g E E' hE)
    (fun m => isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))

/-- **The projective bundle of a pullback is the base change of the projective bundle.** For
`g : X ⟶ Y`, a quasi-coherent `E` on `Y` and a quasi-coherent `E'` on `X` identified with `g^*E`,
the square formed by the comparison morphism, the two projections and `g` is cartesian. -/
public theorem isPullback_projectiveBundleBaseChange :
    IsPullback (projectiveBundleBaseChange g E E' hE) (projectiveBundleToBase X E')
      (projectiveBundleToBase Y E) g :=
  Situation.isPullback_relativeProjBaseChange
    (s := symmetricSituationOfQuasicoherent Y E) (s' := symmetricSituationOfQuasicoherent X E')
    g (symmetricSituationPullbackHom g E E' hE)
    (fun m => isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))

/-- **The comparison isomorphism `𝐏(g^*E) ≅ 𝐏(E) ×_Y X`.** -/
public def projectiveBundleBaseChangeIso :
    projectiveBundle X E' ≅ pullback (projectiveBundleToBase Y E) g :=
  (isPullback_projectiveBundleBaseChange g E E' hE).isoPullback

/-- The comparison isomorphism composed with the projection to `𝐏(E)` is the comparison
morphism. -/
@[simp] public theorem projectiveBundleBaseChangeIso_hom_fst :
    (projectiveBundleBaseChangeIso g E E' hE).hom ≫
        pullback.fst (projectiveBundleToBase Y E) g =
      projectiveBundleBaseChange g E E' hE :=
  (isPullback_projectiveBundleBaseChange g E E' hE).isoPullback_hom_fst

/-- **The comparison isomorphism is a morphism over `X`:** it carries the projection of `𝐏(E')`
to the projection of the fibre product. -/
@[simp] public theorem projectiveBundleBaseChangeIso_hom_snd :
    (projectiveBundleBaseChangeIso g E E' hE).hom ≫
        pullback.snd (projectiveBundleToBase Y E) g =
      projectiveBundleToBase X E' :=
  (isPullback_projectiveBundleBaseChange g E E' hE).isoPullback_hom_snd

/-- The comparison morphism of projective bundles is a morphism over `g`. -/
public theorem projectiveBundleBaseChange_comp_projectiveBundleToBase :
    projectiveBundleBaseChange g E E' hE ≫ projectiveBundleToBase Y E =
      projectiveBundleToBase X E' ≫ g :=
  (isPullback_projectiveBundleBaseChange g E E' hE).w

/-! ### The same square with the base morphism as its first leg

The fibre product `pullback g (projectiveBundleToBase Y E)` is a different object from
`pullback (projectiveBundleToBase Y E) g`, and it is the one over which the comparison is
characterised by its *base* projection. Everything here is the cartesian square above read in
the other orientation. -/

/-- **The base-change square of projective bundles, with the base morphism as its first leg.**
`𝐏(E')` is the fibre product of `g` and the projection of `𝐏(E)`. -/
public theorem isPullback_projectiveBundleToBase_baseChange :
    IsPullback (projectiveBundleToBase X E') (projectiveBundleBaseChange g E E' hE) g
      (projectiveBundleToBase Y E) :=
  (isPullback_projectiveBundleBaseChange g E E' hE).flip

/-- **The comparison isomorphism `𝐏(g^*E) ≅ X ×_Y 𝐏(E)`**, written over the fibre product of
`g` with the projection of `𝐏(E)` — so that its first projection is the projection to the new
base and its second is the comparison morphism. -/
public def projectiveBundleBaseChangeIsoFlip :
    projectiveBundle X E' ≅ pullback g (projectiveBundleToBase Y E) :=
  (isPullback_projectiveBundleToBase_baseChange g E E' hE).isoPullback

/-- **The comparison isomorphism is a morphism over `X`**: composed with the first projection of
`X ×_Y 𝐏(E)` it is the projection of `𝐏(E')`. -/
@[simp] public theorem projectiveBundleBaseChangeIsoFlip_hom_fst :
    (projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
        pullback.fst g (projectiveBundleToBase Y E) =
      projectiveBundleToBase X E' :=
  (isPullback_projectiveBundleToBase_baseChange g E E' hE).isoPullback_hom_fst

/-- The comparison isomorphism composed with the second projection of `X ×_Y 𝐏(E)` is the
comparison morphism. -/
@[simp] public theorem projectiveBundleBaseChangeIsoFlip_hom_snd :
    (projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
        pullback.snd g (projectiveBundleToBase Y E) =
      projectiveBundleBaseChange g E E' hE :=
  (isPullback_projectiveBundleToBase_baseChange g E E' hE).isoPullback_hom_snd

/-- The second projection of the comparison isomorphism is a morphism over `g`. This is the
commutation `b ≫ π = π' ≫ g` for `b` the morphism `𝐏(E') ⟶ 𝐏(E)` read off the comparison with
the fibre product. -/
public theorem projectiveBundleBaseChangeIsoFlip_hom_snd_comp_projectiveBundleToBase :
    ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
        pullback.snd g (projectiveBundleToBase Y E)) ≫ projectiveBundleToBase Y E =
      projectiveBundleToBase X E' ≫ g := by
  rw [projectiveBundleBaseChangeIsoFlip_hom_snd,
    projectiveBundleBaseChange_comp_projectiveBundleToBase]

end Stacks.RelativeProj

end
