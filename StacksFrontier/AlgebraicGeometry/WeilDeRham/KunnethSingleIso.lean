module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.ShiftedSingles
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethSpaceFunctoriality
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeSheafHomComparisonFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbedding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethCupWithClassCanonical
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The global Künneth map at two shifted flat quasi-coherent modules

Let `S` be an affine scheme with `A = Γ(S, 𝒪_S)`, let `a : X ⟶ S` and `b : Y ⟶ S` be
quasi-compact and quasi-separated, let `ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat
over `S`, and let `W` be a scheme with maps `p : W ⟶ X`, `q : W ⟶ Y` exhibiting it as
`X ×_S Y`. For `i, j ∈ ℤ` the global Künneth map of [Stacks, Tag 0G7V]

`RΓ(X, ℱ[-i]) ⊗^𝐋_A RΓ(Y, 𝒢[-j]) ⟶ RΓ(W, Lp^*ℱ[-i] ⊗^𝐋 Lq^*𝒢[-j])`

is an isomorphism in `D(A)` as soon as `a` is flat.

For `W` the fibre product itself, the map is the Leray isomorphisms, the global cup product on
the base at `(Ra_*ℱ[-i], Rb_*𝒢[-j])`, invertible over an affine base, and derived global sections
of the relative Künneth map of [Stacks, Tag 0FLP]. The relative map followed by the comparison
`Lp^*ℱ[-i] ⊗^𝐋 Lq^*𝒢[-j] ⟶ Tot(p^*ℱ[-i] ⊗ q^*𝒢[-j])` is invertible because `𝒢` is flat over `S`;
the comparison itself is invertible because `q`, the base change of the flat `a`, is flat, so
that `Lq^*𝒢 = q^*𝒢`, and because of the Tor vanishing `Lp^*ℱ ⊗^𝐋 q^*𝒢 ≅ p^*ℱ ⊗ q^*𝒢`
([Stacks, Tag 0GMU]). For a general `W` the map is the one through the fibre product followed by
pullback along the isomorphism `W ≅ X ×_S Y`.

## Main definitions

* `Stacks.WeilDeRham.KunnethSingleIso`: the global Künneth map at `ℱ[-i]` and `𝒢[-j]` is an
  isomorphism.

## Main results

* `Stacks.WeilDeRham.isIso_kunnethGlobalMapCanonical_of_isIso_comp`: invertibility of the global
  Künneth map is invariant under pulling back the projections along an isomorphism.
* `Stacks.WeilDeRham.isIso_kunnethMap_singleObj`: the relative Künneth map at `ℱ[-i]`, `𝒢[-j]`
  is invertible.
* `Stacks.WeilDeRham.kunnethSingleIso`: the global Künneth map at `ℱ[-i]`, `𝒢[-j]` is invertible.

## Implementation notes

Some flatness beyond that of `𝒢` over `S` is needed: the target is built from the derived
tensor product of derived pullbacks, which differs from `p^*ℱ ⊗ q^*𝒢` when `X` and `Y` are not
Tor independent over `S`, even for `ℱ` and `𝒢` both flat over `S`. For `A = k[t]`,
`X = Y = Spec k[t, x]/(tx)` and `ℱ = 𝒢 = 𝒪/(x)`, both flat over `A`, the source is
`k[t] ⊗_A k[t] = k[t]` in degree `0`, while `Lp^*ℱ ⊗^𝐋 Lq^*𝒢` has nonzero cohomology in degree
`-2`. Flatness of `a` makes `X` and `Y` Tor independent over `S`; flatness of `ℱ` over `S` is not
used.

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open scoped CategoryTheory.Prod
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

/-- For a bifunctor `T`, `T(α, β)` followed by `t` is invertible when `β` and `T(α, B') ≫ t`
are. -/
private theorem isIso_uncurry_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) {A A' : C} {B B' : D} {Z : E} (α : A ⟶ A') (β : B ⟶ B')
    (t : (T.obj A').obj B' ⟶ Z) (hβ : IsIso β) (h : IsIso ((T.map α).app B' ≫ t)) :
    IsIso ((Functor.uncurry.obj T).map (α ×ₘ β) ≫ t) := by
  have e : (Functor.uncurry.obj T).map (α ×ₘ β) = (T.obj A).map β ≫ (T.map α).app B' := by
    rw [Functor.uncurry_obj_map]
    exact ((T.map α).naturality β).symm
  rw [e, Category.assoc]
  exact IsIso.comp_isIso' inferInstance h

/-- A functor on a product category sends a product of isomorphisms to an isomorphism. -/
private theorem isIso_map_prod_hom {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C × D ⥤ E) {A A' : C} {B B' : D} (α : A ≅ A') (β : B ≅ B') :
    IsIso (T.map (α.hom ×ₘ β.hom)) :=
  (T.mapIso (Iso.prod α β)).isIso_hom

/-- The canonical global Künneth map of [Stacks, Tag 0G7V] at `ℱ[-i]` and `𝒢[-j]`,
`RΓ(X, ℱ[-i]) ⊗^𝐋_A RΓ(Y, 𝒢[-j]) ⟶ RΓ(W, Lp^*ℱ[-i] ⊗^𝐋 Lq^*𝒢[-j])` with `A = Γ(S, 𝒪_S)`,
is an isomorphism. -/
def KunnethSingleIso {S X Y W : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G : Y.Modules)
    (i j : ℤ) (p : W ⟶ X) (q : W ⟶ Y) (hpq : p ≫ a = q ≫ b) : Prop :=
  IsIso (kunnethGlobalMapCanonical a.toLRSHom.toShHom b.toLRSHom.toShHom p.toLRSHom.toShHom
    q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl (by rw [hpq]; rfl)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) i).obj F)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) j).obj G))

/-- **Invertibility of the global Künneth map is invariant under an isomorphism of the
space.**  If the global Künneth map through `W` with projections `p`, `q` is invertible and
`g : W' ⟶ W` is an isomorphism of ringed spaces, the global Künneth map through `W'` with
projections `g ≫ p`, `g ≫ q` is invertible. -/
theorem isIso_kunnethGlobalMapCanonical_of_isIso_comp {S X Y W W' : RingedSpace.{u, u}}
    (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y) (f : W ⟶ S) (hp : p ≫ a = f)
    (hq : q ≫ b = f) (g : W' ⟶ W) [IsIso g] (p' : W' ⟶ X) (q' : W' ⟶ Y) (f' : W' ⟶ S)
    (hp' : p' ≫ a = f') (hq' : q' ≫ b = f') (h₁ : g ≫ p = p') (h₂ : g ≫ q = q')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (kunnethGlobalMapCanonical a b p q f hp hq K M)) :
    IsIso (kunnethGlobalMapCanonical a b p' q' f' hp' hq' K M) := by
  subst h₁ h₂
  obtain rfl : f' = g ≫ f := by rw [← hp', Category.assoc, hp]
  rw [← kunnethGlobalMapCanonical_comp_pullbackSections a b p q f hp hq g K M]
  have hs := isIso_pullbackSections_of_isIso f g (g ≫ f) rfl
    (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
      ((derivedPullback q).obj M))
  have hc : IsIso ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison g).app
      ((derivedPullback p).obj K, (derivedPullback q).obj M)) :=
    Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackTensorComparison_app g _
  have hu := isIso_map_prod_hom (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf))
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g p).app K)
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g q).app M)
  exact IsIso.comp_isIso' h (IsIso.comp_isIso' hs
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (IsIso.comp_isIso' hc hu)))

/-- **The relative Künneth map at two shifted modules is invertible.**  Let `a : X ⟶ S` be flat,
quasi-compact and quasi-separated, `b : Y ⟶ S` quasi-compact and quasi-separated, and `ℱ` on `X`,
`𝒢` on `Y` quasi-coherent with `𝒢` flat over `S`.  For all `i`, `j` the relative Künneth map of
[Stacks, Tag 0FLP] at `ℱ[-i]` and `𝒢[-j]`, with `p`, `q` the projections of `X ×_S Y`,

`Ra_*ℱ[-i] ⊗^𝐋 Rb_*𝒢[-j] ⟶ R(p ≫ a)_*(Lp^*ℱ[-i] ⊗^𝐋 Lq^*𝒢[-j])`,

is an isomorphism. -/
theorem isIso_kunnethMap_singleObj {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) [Flat a]
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hG : IsFlatOver b.toLRSHom.toShHom G) (i j : ℤ) :
    IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
        (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
        ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom) rfl
        (toShHom_pullback_condition a b)
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))) := by
  have hk := AlgebraicGeometry.FlatKunneth.isIso_kunnethMap_comp_toTensor_singleObj a b F G hG i j
  have hτ :=
    Stacks.Cohomology.DerivedBaseChangeComparison.isIso_derivedPullbackNatTrans_app_of_isFlat
    (pullback.snd a b).toLRSHom.toShHom (fun x => Flat.stalkMap _ x)
    ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)
  let eL : (pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj
        ((modulePullback (pullback.snd a b).toLRSHom.toShHom).obj G) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (modulePullback (pullback.snd a b).toLRSHom.toShHom) (ComplexShape.up ℤ) j).app G
  have : SheafOfModules.IsQuasicoherent
      (show SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) from G) :=
    inferInstanceAs G.IsQuasicoherent
  have h4 :=
    AlgebraicGeometry.FlatKunneth.isIso_derivedTensor_derivedPullbackNatTrans_toTensor_fibre
    a b G hG ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F)
    ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
      ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) j eL
  have hc : IsIso ((Functor.uncurry.obj
        (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
        ((derivedPullbackNatTrans (pullback.fst a b).toLRSHom.toShHom).app
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F) ×ₘ
          (derivedPullbackNatTrans (pullback.snd a b).toLRSHom.toShHom).app
            ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G)) ≫
      (canonicalDerivedTensorProduct (pullback a b).toRingedSpace.sheaf).toTensor
        ((pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))
        ((pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj
          ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))) :=
    isIso_uncurry_map_comp _ _ _ _ hτ h4
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ hc) hk

/-- **The global Künneth map at two shifted modules is an isomorphism.**  Let `S` be affine with
`A = Γ(S, 𝒪_S)`, let `a : X ⟶ S` be flat, quasi-compact and quasi-separated and `b : Y ⟶ S`
quasi-compact and quasi-separated, let `ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat
over `S`, and let `p : W ⟶ X`, `q : W ⟶ Y` be the projections of `X ×_S Y` read through an
isomorphism `W ≅ X ×_S Y`.  For all `i`, `j` the global Künneth map of [Stacks, Tag 0G7V]

`RΓ(X, ℱ[-i]) ⊗^𝐋_A RΓ(Y, 𝒢[-j]) ⟶ RΓ(W, Lp^*ℱ[-i] ⊗^𝐋 Lq^*𝒢[-j])`

is an isomorphism in `D(A)`. -/
theorem kunnethSingleIso {S X Y W : Scheme.{u}} [IsAffine S] (a : X ⟶ S) (b : Y ⟶ S) [Flat a]
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hG : IsFlatOver b.toLRSHom.toShHom G) (i j : ℤ) (p : W ⟶ X) (q : W ⟶ Y)
    (e : W ≅ pullback a b) (he₁ : e.hom ≫ pullback.fst a b = p)
    (he₂ : e.hom ≫ pullback.snd a b = q) (hpq : p ≫ a = q ≫ b) :
    KunnethSingleIso a b F G i j p q hpq := by
  subst he₁ he₂
  have hF0 := AlgebraicGeometry.FlatKunneth.isQCohAll_Q_singleObj F i
  have hG0 := AlgebraicGeometry.FlatKunneth.isQCohAll_Q_singleObj G j
  have hκ := AlgebraicGeometry.FlatKunneth.isIso_globalCupProductCanonical_app S _ _
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward a hF0)
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward b hG0)
  have hrel := isIso_kunnethMap_singleObj a b F G hG i j
  have hA := isIso_map_prod_hom (Functor.uncurry.obj (tensorBase S.toRingedSpace))
    ((lerayIso a.toLRSHom.toShHom).app (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))).symm
    ((lerayIso b.toLRSHom.toShHom).app (DerivedCategory.Q.obj
      ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))).symm
  have hbase : IsIso (kunnethGlobalMapCanonical a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom) rfl
      (toShHom_pullback_condition a b)
      (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F))
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G))) :=
    IsIso.comp_isIso' hA (IsIso.comp_isIso' hκ
      (IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hrel)
        ((lerayIso ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom)).app _).isIso_hom))
  have hK : (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) i).obj F =
      DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F) :=
    rfl
  have hM : (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing Y.toRingedSpace)) j).obj G =
      DerivedCategory.Q.obj ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G) :=
    rfl
  unfold KunnethSingleIso
  rw [hK, hM]
  exact isIso_kunnethGlobalMapCanonical_of_isIso_comp a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom) rfl
    (toShHom_pullback_condition a b) e.hom.toLRSHom.toShHom
    (e.hom ≫ pullback.fst a b).toLRSHom.toShHom (e.hom ≫ pullback.snd a b).toLRSHom.toShHom
    ((e.hom ≫ pullback.fst a b) ≫ a).toLRSHom.toShHom
    (by rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom])
    (by rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom, Category.assoc,
      ← pullback.condition, ← Category.assoc])
    (by rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom])
    (by rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom]) _ _ hbase

end Stacks.WeilDeRham

end
