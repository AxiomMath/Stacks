module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat resolutions on a ringed site with the module universe free of the site

Stacks Tag 06YS for a ringed site whose object and morphism universes are independent of the
universe of the sections of its structure sheaf: every complex of `O`-modules admits a termwise
surjective quasi-isomorphism from a K-flat complex with flat terms.

The resolution is the colimit of the ladder of Stacks 077J, whose construction (Stacks 06XX,
`CochainComplex.exists_sequence_quasiIso_truncLE`) is abstract in the class of objects used to
resolve: it asks only that the class contain a zero object, be closed under binary biproducts,
and have every object of the category as a quotient of one of its members. Taking that class to
be flatness itself, those three inputs are
`Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize`, `isFlat_biprod_ofSize` and
`Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize`, all three with the module
universe equal to the ring universe and the two site universes free.

## Main results

* `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize`: the resolution
  presented as a sequential colimit of bounded above complexes of flat modules.
* `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`: **Stacks 06YS** at
  those universes.
* `Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize`: the same, in the shape
  the abstract K-flat localization of `CochainComplex.KFlatBifunctor` consumes.
* `Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize`: the total complex of a double
  complex of `O`-modules exists, which is what the K-flatness criteria need of `Mod(O)`.
* `Stacks.SheafOfModules.KFlatResolution.hasColimits_ofSize`: `Mod(O)` has all colimits where
  the module universe contains the object universe.

## Universes

The module universe equals the ring universe, which the flat cover forces, and the object and
morphism universes of the site are free; no result here carries a size hypothesis relating
them.

The K-flatness criteria of `CochainComplex.KFlatBifunctor` need of `Mod(O)` only colimits of
shapes in `Type 0`, because the total tensor complex is in each degree the coproduct of the
terms along an antidiagonal `p + r = n`. Those are available at every pair of site universes,
which is `hasTotal_ofSize`. By contrast `HasColimits (ModOfSize R)` is a genuine size
condition: the morphism universe of `Mod(O)` is the maximum of the object universe of the site
and the module universe, so colimits of every shape that universe admits are not available when
the module universe is smaller. `hasColimits_ofSize` provides them whenever the object universe
is at most the module universe.

In particular the results here apply to a `RingedTopos.{u, u + 1, u}`, such as the small étale
site of an algebraic space, with no transport to a small model of the site. The small étale site
of a scheme over a big étale site, ringed by the constant coefficient sheaf of Stacks 03TR, has
object universe `u + 1`, morphism universe `u` and module universe `max (u + 1) w r`.

## Implementation notes

Each declaration generalises the declaration of the same name without the `OfSize` suffix in
`StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/ResolutionsOnARingedSite.lean`, which fixes
all four universes to one `u` and carries `SmallCategory`. There the ladder is resolved by
direct sums of extensions by zero `j_{U!}O_U`, whose flatness rests on
`Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`, and that pins the ring universe to
the *morphism* universe of the site, where Mathlib states the universal property it uses.
Resolving by flat modules instead avoids extensions by zero altogether; the terms of the ladder
here are merely flat.

The quasi-isomorphy of the colimit comparison map is
`StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE`, stated for an
arbitrary abelian category: in each fixed degree the homology of the ladder is eventually constant,
and homology commutes with the colimit because sequential colimits of `O`-modules are exact.

Sequential colimits of `O`-modules are exact, and `X ⊗_O -` commutes with them, at every pair of
site universes: the first is Stacks 03DB in the four-universe form
`AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules`, the second Stacks 05NB in the form
`Stacks.SheafOfModules.preservesColimits_sheafTensorObj`. Both are stated for diagrams indexed in
the module universe and are shrunk to `ℕ`.

## References

* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.KFlatResolution

/-! ### The resolution -/

section Resolution

noncomputable section

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- `Mod(O)`, the sheaves of `O`-modules on the ringed site, at a module universe equal to the
ring universe and containing the object universe of the site. -/
abbrev ModOfSize :=
  _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)

/-- Sheaves of modules on the ringed site have colimits of every shape in `Type 0`. -/
private lemma hasColimitsOfSize_zero_ofSize : HasColimitsOfSize.{0, 0} (ModOfSize.{v, u, w} R) := by
  let _ : HasColimitsOfSize.{0, 0}
      (PresheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R).obj) :=
    inferInstance
  infer_instance

/-- Sheaves of modules on the ringed site have sequential colimits. -/
lemma hasColimitsOfShape_nat_ofSize : HasColimitsOfShape ℕ (ModOfSize.{v, u, w} R) :=
  have := hasColimitsOfSize_zero_ofSize.{v, u, w} R
  inferInstance

/-- **The total complex of a double complex of `O`-modules exists**, at every pair of site
universes and with no size condition on the module universe: in each total degree it is the
coproduct of the terms `Z^{p,r}` along the antidiagonal `p + r = n`, a family indexed by a
subtype of `ℤ × ℤ`, and `Mod(O)` has colimits of every shape in `Type 0` whatever its module
universe. This is what the K-flatness criteria of `CochainComplex.KFlatBifunctor` need of
`Mod(O)`; `HasColimits (ModOfSize R)`, which needs the module universe to contain the object
universe of the site, is not required. -/
lemma hasTotal_ofSize :
    ∀ K : HomologicalComplex₂ (ModOfSize.{v, u, w} R)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ), K.HasTotal (ComplexShape.up ℤ) := by
  have := hasColimitsOfSize_zero_ofSize.{v, u, w} R
  exact fun _ ↦ inferInstance

/-- **Sequential colimits of sheaves of modules are exact**, which is Stacks 03DB at a shape
shrunk to `ℕ`. -/
lemma hasExactColimitsOfShape_nat_ofSize :
    HasExactColimitsOfShape ℕ (ModOfSize.{v, u, w} R) := by
  let _ : AB5OfSize.{w, w} (ModOfSize.{v, u, w} R) :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules _
  let _ : AB5OfSize.{0, 0} (ModOfSize.{v, u, w} R) := AB5OfSize_shrink _
  exact AB5OfSize.ofShape ℕ

/-- `X ⊗_O -` commutes with sequential colimits, which is Stacks 05NB at a shape shrunk to `ℕ`.
This is the hypothesis `hF` of the K-flatness criteria of Stacks 06YQ. -/
lemma hF_sheafTensor_ofSize :
    ∀ X : ModOfSize.{v, u, w} R,
      PreservesColimitsOfShape ℕ
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj X) := by
  intro X
  have : PreservesColimitsOfSize.{w, w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj X) :=
    Stacks.SheafOfModules.preservesColimits_sheafTensorObj R X
  have : PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj X) :=
    preservesSmallestColimits_of_preservesColimits _
  infer_instance

/-- A sequential colimit of acyclic complexes of `O`-modules is acyclic, stated at an arbitrary
colimit cocone. This is the hypothesis `hexact` of the K-flatness criteria of Stacks 06YQ. -/
lemma hexact_sheafOfModules_ofSize :
    ∀ (E : ℕ ⥤ CochainComplex (ModOfSize.{v, u, w} R) ℤ) (s : Cocone E),
      IsColimit s → (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic := by
  have := hasColimitsOfShape_nat_ofSize R
  have := hasExactColimitsOfShape_nat_ofSize R
  intro E s hs hE n
  exact (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

/-- **The terms of a sequential colimit of complexes with flat terms are flat**, by Stacks
03EU: evaluation in a degree commutes with the colimit. -/
theorem isFlat_colimit_X_ofSize (D : ℕ ⥤ CochainComplex (ModOfSize.{v, u, w} R) ℤ)
    (hflat : ∀ (n : ℕ) (i : ℤ),
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
        ((D.obj n).X i))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
      ((colimit D).X i) := by
  have := hasColimitsOfShape_nat_ofSize R
  have hcol := @Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit_ofSize C inferInstance J
    ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}› ‹HasWeakSheafify J AddCommGrpCat.{w}›
    R ℕ inferInstance (hasColimitsOfShape_nat_ofSize R) (hasExactColimitsOfShape_nat_ofSize R)
    (D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) i) (fun n ↦ hflat n i)
  exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize R
    (preservesColimitIso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) D).symm hcol

/-- **The resolution of Stacks 06YS, presented as a sequential colimit.** Every complex of
`O`-modules receives a termwise surjective quasi-isomorphism from the colimit of a sequence of
bounded above complexes of flat `O`-modules. -/
theorem exists_resolution_colimit_ofSize (G : CochainComplex (ModOfSize.{v, u, w} R) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (ModOfSize.{v, u, w} R) ℤ) (f : colimit D ⟶ G),
      (∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b) ∧
      (∀ (n : ℕ) (i : ℤ),
        AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
          ((D.obj n).X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  have := hasColimitsOfShape_nat_ofSize R
  have := hasExactColimitsOfShape_nat_ofSize R
  let P : ObjectProperty (ModOfSize.{v, u, w} R) := fun X ↦
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) X
  let _ : P.ContainsZero := Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize R
  have hsum : ∀ X Y, P X → P Y → P (X ⊞ Y) := fun X Y hX hY ↦
    Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize R X Y hX hY
  have hcover : ∀ X, ∃ (Y : _) (_ : P Y) (p : Y ⟶ X), Epi p := by
    intro X
    obtain ⟨N, p, hN, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize R X
    exact ⟨N, hN, p, hp⟩
  obtain ⟨Q, q, g, hq, hepi, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hcover G
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n ↦ q n ≫ G.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ G := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ G.ιTruncLE (n : ℤ) := fun n ↦ hc.fac s n
  refine ⟨D, α, fun n ↦ ⟨(n : ℤ), hle n⟩, fun n i ↦ hflat n i,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq hc α hα,
    fun i ↦ ?_⟩
  have hlt : i < ((i.toNat + 1 : ℕ) : ℤ) := by
    have := Int.self_le_toNat i
    push_cast
    omega
  have h1 : Epi ((q (i.toNat + 1)).f i) := hepi (i.toNat + 1) i
  have h2 : Epi ((G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    G.epi_ιTruncLE_f_of_lt _ i hlt
  have hfac : (c.ι.app (i.toNat + 1)).f i ≫ α.f i
      = (q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i :=
    congrArg (fun φ ↦ φ.f i) (hα (i.toNat + 1))
  have h3 : Epi ((q (i.toNat + 1)).f i ≫ (G.ιTruncLE ((i.toNat + 1 : ℕ) : ℤ)).f i) :=
    @epi_comp _ _ _ _ _ _ h1 _ h2
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ h3 hfac

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K L : CochainComplex (ModOfSize.{v, u, w} R) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) (ComplexShape.up ℤ)]

/-- **A flat module placed in a single degree gives a K-flat complex**, which is the base case
of Stacks 06YQ: tensoring on the right with a flat module is an exact functor, so it carries
acyclic complexes to acyclic ones. -/
theorem kFlat_single_of_isFlat_ofSize (M : ModOfSize.{v, u, w} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M) (q : ℤ) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1
    ((Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor_ofSize R M).1 hM)
  refine CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ M q (fun G hG ↦ ?_)
  exact HomologicalComplex.Acyclic.map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj M) hG

/-- **A sequential colimit of bounded above complexes of flat `O`-modules is K-flat**: each
stage is K-flat by Stacks 06YQ and K-flatness passes to the colimit by Stacks 06YR. -/
theorem kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
    (D : ℕ ⥤ CochainComplex (ModOfSize.{v, u, w} R) ℤ)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ),
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
        ((D.obj n).X i)) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
      (colimit D) := by
  have := hasColimitsOfShape_nat_ofSize R
  have := hasTotal_ofSize R
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ (colimit.cocone D)
    (colimit.isColimit _) (hF_sheafTensor_ofSize R) (hexact_sheafOfModules_ofSize R)
    (fun n ↦ ?_)
  obtain ⟨b, hb⟩ := hLE n
  have := hb
  exact CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ (D.obj n) b
    (hF_sheafTensor_ofSize R) (hexact_sheafOfModules_ofSize R)
    (fun q ↦ kFlat_single_of_isFlat_ofSize R _ (hflat n q) q)

/-- **Stacks Tag 06YS with the module universe free of the site.** Every complex of `O`-modules
on a ringed site admits a termwise surjective quasi-isomorphism from a K-flat complex whose
terms are flat: the colimit of the ladder of Stacks 077J, resolved by flat modules.

The object universe `u`, the morphism universe `v` and the module universe `w` are
independent, so the statement applies at a site whose objects lie above the module universe,
such as the small étale site of an algebraic space, a `RingedTopos.{u, u + 1, u}`. -/
@[stacks 06YS "with the object and morphism universes of the site independent of the module
  universe, so that it applies at a site whose objects lie above the module universe"]
theorem exists_kFlatResolution_ofSize (G : CochainComplex (ModOfSize.{v, u, w} R) ℤ) :
    ∃ (K : CochainComplex (ModOfSize.{v, u, w} R) ℤ) (f : K ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
        (K.X i)) ∧
      QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  obtain ⟨D, f, hLE, hflat, hqis, hepi⟩ := exists_resolution_colimit_ofSize R G
  exact ⟨colimit D, f, kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize R D hLE hflat,
    isFlat_colimit_X_ofSize R D hflat, hqis, hepi⟩

/-- **Every complex of `O`-modules receives a quasi-isomorphism from a K-flat complex**, in the
shape `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization` consumes: the flatness and
surjectivity clauses of Stacks 06YS forgotten, and K-flatness spelled as
`Stacks.SheafOfModules.IsKFlat`. -/
theorem exists_kFlat_quasiIso_ofSize (G : CochainComplex (ModOfSize.{v, u, w} R) ℤ) :
    ∃ (P : CochainComplex (ModOfSize.{v, u, w} R) ℤ) (p : P ⟶ G),
      Stacks.SheafOfModules.IsKFlat R P ∧ QuasiIso p := by
  obtain ⟨K, f, hK, -, hf, -⟩ := exists_kFlatResolution_ofSize R G
  exact ⟨K, f, fun F hF ↦ hK F hF, hf⟩

/-! ### The size condition on the module universe -/

section HasColimits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u w}]

/-- Sheaves of modules on the ringed site have colimits of every shape their own morphism
universe admits, as soon as the module universe contains the object universe of the site. -/
lemma hasColimits_ofSize (R : Sheaf J CommRingCat.{max u w}) :
    HasColimits (ModOfSize.{v, u, max u w} R) := by
  let _ : HasColimitsOfSize.{max u w, max u w}
      (PresheafOfModules.{max u w}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u w} R).obj) :=
    inferInstance
  infer_instance

end HasColimits

end

end Resolution

end Stacks.SheafOfModules.KFlatResolution

end
