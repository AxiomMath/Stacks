module

public import StacksFrontier.AlgebraicGeometry.PullbackTildeComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel

/-!
# The affine comparison square composes

Let `f : R ⟶ S` and `g : S ⟶ T` be homomorphisms of commutative rings. Part (2) of
[Stacks, Tag 08DW] compares derived pullback along `Spec f` with derived extension of scalars,

  `Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`,

and `AlgebraicGeometry.StandardModel.affinePullbackComparison` is that comparison at the standard
model of the derived category. This file proves that the comparison is compatible with
composition of ring maps: the comparison for `f ≫ g` is the comparison for `f`, pushed along
`Lg^*`, followed by the comparison for `g`, read through the composition isomorphism of
[Stacks, Tag 0D5S] for derived pullback and the composition isomorphism of [Stacks, Tag 06YJ] for
derived extension of scalars.

## Main results

* `AlgebraicGeometry.affinePullbackComparison_comp` — **the composition compatibility**, at an
  object of `D(R)`, and `AlgebraicGeometry.affinePullbackComparison_comp_hom` — the same identity
  as an equality of natural transformations.
* `StacksDraft.ComparisonSquare.comp_app` — the chase, for arbitrary categories, functors and
  comparison maps: two comparison squares whose underlying degreewise squares, derived pullbacks
  and derived extensions of scalars all compose, compose.
* `StacksDraft.ComparisonSquare.mapHomologicalComplex_cocycle` — a cocycle of natural
  transformations passes to complexes, degreewise, again for arbitrary functors.
* `AlgebraicGeometry.specPullbackComp_inv` — the degreewise composition isomorphism
  `AlgebraicGeometry.StandardModel.specPullbackComp` of pullbacks along `Spec f` and `Spec g` is
  inverse to `AlgebraicGeometry.pullbackSpecMapCompIso`.
* `AlgebraicGeometry.tildePullbackComplexIso_comp` — the composition compatibility of
  [Stacks, Tag 01I9] on complexes: the degreewise affine-pullback isomorphism for `f ≫ g` is the
  one for `f`, then the one for `g`, read through the two degreewise composition isomorphisms.
* `AlgebraicGeometry.affinePullbackComparison_hom_app_Q` — the pinning equation of
  `AlgebraicGeometry.StandardModel.affinePullbackComparison_fac` with every whiskering evaluated.
* `AlgebraicGeometry.StandardModel.specPullbackComplexComparison_comp` and
  `AlgebraicGeometry.totalDerivedExtensionScalarsComp_comparison_Q` — the composition laws of
  [Stacks, Tag 0D5S] and [Stacks, Tag 06Y5].
* `AlgebraicGeometry.affinePullbackComparisonComp_app` — the whiskered composite of the two
  affine comparison squares, evaluated at an object of `D(R)`.
* `AlgebraicGeometry.affinePullbackComparisonComp_comparisons_Q`,
  `AlgebraicGeometry.affinePullbackComparisonComp_pullbackComp_Q` and
  `AlgebraicGeometry.affinePullbackComparisonComp_degreewise_Q` — the three groups of squares at
  the concrete data, joined by `AlgebraicGeometry.affinePullbackComparison_comp_app_Q`.

## Implementation notes

*Why the chase is abstracted, and why it is split.* The identity is an equality of two natural
transformations into a total left derived functor, so `CategoryTheory.Functor.leftDerived_ext`
reduces it to an equality at `DerivedCategory.Q.obj M` for a complex `M` of `R`-modules, where the
left-hand leg is exactly `AlgebraicGeometry.StandardModel.affinePullbackComparison_fac`. The
right-hand leg is a chase of eight squares between objects of derived categories of sheaves of
modules, and performed on those concrete functors each rewrite pays for a traversal of a term
carrying three schemes, three rings and two presentations of each derived category.
`StacksDraft.ComparisonSquare.comp_app` performs the same chase on variables: nothing in it is
about sheaves, and none of the natural transformations involved needs to be invertible, so it
takes eighteen natural transformations and five hypotheses and no isomorphisms at all.

One application of it at the concrete data is nevertheless more than the kernel will recheck, so
the chase is factored into three groups of squares — the two comparison squares with the
composition law of the extensions of scalars (`comp_app_comparisons`), the derived-pullback
squares (`comp_app_pullbackComp`), and the degreewise cocycle after localisation
(`comp_app_degreewise`) — each quantified over only the natural transformations its own squares
mention, and `comp_app` is their composite. At the concrete data the three are instantiated in
three separate declarations and joined by
`AlgebraicGeometry.affinePullbackComparison_comp_app_Q`, so that no declaration carries all
eighteen transformations at once.

*Where a composite functor must not appear in a type.* Instantiating a variable natural
transformation whose type names a composite functor forces the kernel to decide an equality of two
functors, not of their values, and at these concrete functors that is the one check that cannot be
afforded. Two such transformations arise. The composition of the degreewise pullbacks is a
morphism out of `(f^• ⋙ g^•)` on one side and into `f^• ⋙ g^•` on the other; its naturality is
never used, so `comp_app_pullbackComp` and `comp_app_degreewise` take it componentwise, and the
check left over is the equality of two sheaves of modules. The composition isomorphism of
Tag 0D5S has type `Lf^* ⋙ Lg^* ≅ L(f ≫ g)^*` and its naturality *is* used, so the concrete
derived-pullback leg `AlgebraicGeometry.affinePullbackComparisonComp_pullbackComp_Q` is the one
leg written out on the concrete comparisons rather than instantiated from
`comp_app_pullbackComp`: three naturality squares on the concrete data, each an equality of
values.

*Two conversions the kernel cannot afford.* Two spellings of one notion meet here, and in both
cases the resulting conversion check must be kept out of the finished proof term rather than
merely out of the elaborator. The first is the term of degree `n` of a degreewise image of a
complex: `((F^•).obj M).X n` and `F.obj (M.X n)` are equal by definition, but checking that
against `AlgebraicGeometry.Scheme.Modules.pullback` unfolds the construction of a pullback of
sheaves of modules and exhausts the kernel's budget, so the degreewise check is performed by
`StacksDraft.ComparisonSquare.mapHomologicalComplex_cocycle`, whose functors are variables.
The second is `AlgebraicGeometry.StandardModel.specPullbackComp`: delta-unfolding it, which is
what matching the statement of
`AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison_comp_schemeFactorIso` asks for,
has the same effect, so that composition isomorphism is written out as
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` throughout. Neither is a matter of taste; with
either conversion left in the term the file reports `(kernel) deterministic timeout` and no
elaboration error.

*Why `Spec.map_comp` rides inside the composition isomorphism.* `Spec.map (f ≫ g)` is not
syntactically `Spec.map g ≫ Spec.map f`, so the composition isomorphism of Tag 0D5S for the two
morphisms of affine schemes is not literally an isomorphism onto derived pullback along
`Spec (f ≫ g)`; the transport is carried by
`Stacks.DerivedPullback.schemeFactorIso`, which takes the factorisation as a hypothesis. By
contrast `(f ≫ g).hom` *is* `g.hom.comp f.hom`, so no transport is needed on the ring side and
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` applies as it stands.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace StacksDraft.ComparisonSquare

/-! ### The chase, for arbitrary categories and comparison maps -/

variable {CR DR CS DS CT DT CR' DR' CS' DS' CT' DT' : Type*}
  [Category* CR] [Category* DR] [Category* CS] [Category* DS] [Category* CT] [Category* DT]
  [Category* CR'] [Category* DR'] [Category* CS'] [Category* DS'] [Category* CT'] [Category* DT']
  {QR : CR ⥤ DR} {QS : CS ⥤ DS} {QT : CT ⥤ DT}
  {QR' : CR' ⥤ DR'} {QS' : CS' ⥤ DS'} {QT' : CT' ⥤ DT'}
  {tR : CR ⥤ CR'} {tS : CS ⥤ CS'} {tT : CT ⥤ CT'}
  {TR : DR ⥤ DR'} {TS : DS ⥤ DS'} {TT : DT ⥤ DT'}
  {pf : CR' ⥤ CS'} {pg : CS' ⥤ CT'} {pk : CR' ⥤ CT'}
  {Pf : DR' ⥤ DS'} {Pg : DS' ⥤ DT'} {Pk : DR' ⥤ DT'}
  {ef : CR ⥤ CS} {eg : CS ⥤ CT} {ek : CR ⥤ CT}
  {Ef : DR ⥤ DS} {Eg : DS ⥤ DT} {Ek : DR ⥤ DT}

/-- **The comparison half of the chase.** Four squares: the composition law `hΨ` of the two
extensions of scalars, the naturality of `mT` at `ε` and of `Ag` at `cf`, and the normalisations
`hg` and `hf` of the two derived comparisons. Together they rewrite the composite of `Af` and
`Ag`, read through `Ψ` and the normalisation `ck` of the composite extension of scalars, into the
normalisation of `Af` pushed along `Pg` followed by the comparison `dg` and the degreewise `τg`
and `ε`. -/
theorem comp_app_comparisons
    (mR : QR ⋙ TR ⟶ tR ⋙ QR') (mS : QS ⋙ TS ⟶ tS ⋙ QS') (mT : QT ⋙ TT ⟶ tT ⋙ QT')
    (df : QR' ⋙ Pf ⟶ pf ⋙ QS') (dg : QS' ⋙ Pg ⟶ pg ⋙ QT')
    (cf : QR ⋙ Ef ⟶ ef ⋙ QS) (cg : QS ⋙ Eg ⟶ eg ⋙ QT) (ck : QR ⋙ Ek ⟶ ek ⋙ QT)
    (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT)
    (Ψ : Ef ⋙ Eg ⟶ Ek) (ε : ef ⋙ eg ⟶ ek)
    (Af : TR ⋙ Pf ⟶ Ef ⋙ TS) (Ag : TS ⋙ Pg ⟶ Eg ⋙ TT)
    (hf : ∀ M : CR, Af.app (QR.obj M) ≫ TS.map (cf.app M) ≫ mS.app (ef.obj M) =
      Pf.map (mR.app M) ≫ df.app (tR.obj M) ≫ QS'.map (τf.app M))
    (hg : ∀ N : CS, Ag.app (QS.obj N) ≫ TT.map (cg.app N) ≫ mT.app (eg.obj N) =
      Pg.map (mS.app N) ≫ dg.app (tS.obj N) ≫ QT'.map (τg.app N))
    (hΨ : ∀ M : CR, Eg.map (cf.app M) ≫ cg.app (ef.obj M) ≫ QT.map (ε.app M) =
      Ψ.app (QR.obj M) ≫ ck.app M)
    (M : CR) :
    Pg.map (Af.app (QR.obj M)) ≫ Ag.app (Ef.obj (QR.obj M)) ≫
        TT.map (Ψ.app (QR.obj M)) ≫ TT.map (ck.app M) ≫ mT.app (ek.obj M) =
      Pg.map (Pf.map (mR.app M)) ≫ Pg.map (df.app (tR.obj M)) ≫
        Pg.map (QS'.map (τf.app M)) ≫ dg.app (tS.obj (ef.obj M)) ≫
        QT'.map (τg.app (ef.obj M)) ≫ QT'.map (tT.map (ε.app M)) := by
  have n1 := mT.naturality (ε.app M)
  have n2 := Ag.naturality (cf.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1 n2
  rw [← Functor.map_comp_assoc TT (Ψ.app (QR.obj M)) (ck.app M), ← hΨ M]
  simp only [Functor.map_comp, Category.assoc]
  rw [n1, ← reassoc_of% n2]
  rw [reassoc_of% (hg (ef.obj M))]
  rw [← Functor.map_comp_assoc Pg (TS.map (cf.app M)) (mS.app (ef.obj M)),
    ← Functor.map_comp_assoc Pg (Af.app (QR.obj M))
      (TS.map (cf.app M) ≫ mS.app (ef.obj M)), hf M]
  simp only [Functor.map_comp, Category.assoc]

/-- **The derived-pullback squares of the chase.** Three squares: the naturality of `dg` at `τf`
and of `Φ` at `mR`, and the composition law `hΦ` of the pullbacks. Together they rewrite the
normalisation of `Af` pushed along `Pg`, followed by the comparison `dg`, into the comparison `dk`
for the composite followed by the localisation of `μ` and of `τf`. The composition `μ` of the
degreewise functors along the top is taken componentwise. -/
theorem comp_app_pullbackComp
    (mR : QR ⋙ TR ⟶ tR ⋙ QR')
    (df : QR' ⋙ Pf ⟶ pf ⋙ QS') (dg : QS' ⋙ Pg ⟶ pg ⋙ QT') (dk : QR' ⋙ Pk ⟶ pk ⋙ QT')
    (τf : tR ⋙ pf ⟶ ef ⋙ tS)
    (Φ : Pk ⟶ Pf ⋙ Pg) (μ : ∀ K : CR', pk.obj K ⟶ pg.obj (pf.obj K))
    (hΦ : ∀ K : CR', Φ.app (QR'.obj K) ≫ Pg.map (df.app K) ≫ dg.app (pf.obj K) =
      dk.app K ≫ QT'.map (μ K))
    (M : CR) :
    Φ.app (TR.obj (QR.obj M)) ≫ Pg.map (Pf.map (mR.app M)) ≫ Pg.map (df.app (tR.obj M)) ≫
        Pg.map (QS'.map (τf.app M)) ≫ dg.app (tS.obj (ef.obj M)) =
      Pk.map (mR.app M) ≫ dk.app (tR.obj M) ≫ QT'.map (μ (tR.obj M)) ≫
        QT'.map (pg.map (τf.app M)) := by
  have n3 := dg.naturality (τf.app M)
  have n4 := Φ.naturality (mR.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n3 n4
  rw [n3, ← reassoc_of% n4, reassoc_of% (hΦ (tR.obj M))]

/-- **The degreewise cocycle, read after localisation.** The localisation of the four degreewise
morphisms of `hdeg` is the localisation of `τk`. -/
theorem comp_app_degreewise
    (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT) (τk : tR ⋙ pk ⟶ ek ⋙ tT)
    (ε : ef ⋙ eg ⟶ ek) (μ : ∀ K : CR', pk.obj K ⟶ pg.obj (pf.obj K))
    (hdeg : ∀ M : CR, μ (tR.obj M) ≫ pg.map (τf.app M) ≫ τg.app (ef.obj M) ≫
      tT.map (ε.app M) = τk.app M)
    (M : CR) :
    QT'.map (μ (tR.obj M)) ≫ QT'.map (pg.map (τf.app M)) ≫ QT'.map (τg.app (ef.obj M)) ≫
        QT'.map (tT.map (ε.app M)) = QT'.map (τk.app M) := by
  simp only [← Functor.map_comp]
  rw [hdeg M]

/-- **The pullback half of the chase.** Four squares: the three of `comp_app_pullbackComp` and
the degreewise cocycle of `comp_app_degreewise`. Together they rewrite the normalisation of `Af`
pushed along `Pg`, followed by `dg` and the degreewise `τg` and `ε`, into the normalisation of a
derived comparison for the composite. -/
theorem comp_app_pullback
    (mR : QR ⋙ TR ⟶ tR ⋙ QR')
    (df : QR' ⋙ Pf ⟶ pf ⋙ QS') (dg : QS' ⋙ Pg ⟶ pg ⋙ QT') (dk : QR' ⋙ Pk ⟶ pk ⋙ QT')
    (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT) (τk : tR ⋙ pk ⟶ ek ⋙ tT)
    (Φ : Pk ⟶ Pf ⋙ Pg) (μ : ∀ K : CR', pk.obj K ⟶ pg.obj (pf.obj K)) (ε : ef ⋙ eg ⟶ ek)
    (hΦ : ∀ K : CR', Φ.app (QR'.obj K) ≫ Pg.map (df.app K) ≫ dg.app (pf.obj K) =
      dk.app K ≫ QT'.map (μ K))
    (hdeg : ∀ M : CR, μ (tR.obj M) ≫ pg.map (τf.app M) ≫ τg.app (ef.obj M) ≫
      tT.map (ε.app M) = τk.app M)
    (M : CR) :
    Φ.app (TR.obj (QR.obj M)) ≫ Pg.map (Pf.map (mR.app M)) ≫ Pg.map (df.app (tR.obj M)) ≫
        Pg.map (QS'.map (τf.app M)) ≫ dg.app (tS.obj (ef.obj M)) ≫
        QT'.map (τg.app (ef.obj M)) ≫ QT'.map (tT.map (ε.app M)) =
      Pk.map (mR.app M) ≫ dk.app (tR.obj M) ≫ QT'.map (τk.app M) := by
  rw [reassoc_of% (comp_app_pullbackComp mR df dg dk τf Φ μ hΦ M),
    comp_app_degreewise τf τg τk ε μ hdeg M]

/-- **Two comparison squares compose.** The data is two columns of a comparison square: on the
left the degreewise functors `tR`, `tS`, `tT` with their derived counterparts `TR`, `TS`, `TT`
pinned by `mR`, `mS`, `mT`; along the top the degreewise pullbacks `pf`, `pg`, `pk` with their
derived counterparts `Pf`, `Pg`, `Pk` pinned by `df`, `dg`, `dk`; along the bottom the degreewise
extensions of scalars `ef`, `eg`, `ek` with their derived counterparts `Ef`, `Eg`, `Ek` pinned by
`cf`, `cg`, `ck`; the degreewise comparisons `τf`, `τg`, `τk`; and the derived comparisons `Af`,
`Ag` normalised against the degreewise ones by `hf` and `hg`.

If the three columns compose — `Φ` and `μ` for pullback (`hΦ`), `Ψ` and `ε` for extension of
scalars (`hΨ`), and the degreewise cocycle `hdeg` — then so do the derived comparisons: the
composite of `Af` and `Ag`, read through `Φ` and `Ψ`, satisfies the normalisation of a derived
comparison for the composite. No morphism here is required to be invertible. -/
theorem comp_app
    (mR : QR ⋙ TR ⟶ tR ⋙ QR') (mS : QS ⋙ TS ⟶ tS ⋙ QS') (mT : QT ⋙ TT ⟶ tT ⋙ QT')
    (df : QR' ⋙ Pf ⟶ pf ⋙ QS') (dg : QS' ⋙ Pg ⟶ pg ⋙ QT') (dk : QR' ⋙ Pk ⟶ pk ⋙ QT')
    (cf : QR ⋙ Ef ⟶ ef ⋙ QS) (cg : QS ⋙ Eg ⟶ eg ⋙ QT) (ck : QR ⋙ Ek ⟶ ek ⋙ QT)
    (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT) (τk : tR ⋙ pk ⟶ ek ⋙ tT)
    (Φ : Pk ⟶ Pf ⋙ Pg) (Ψ : Ef ⋙ Eg ⟶ Ek) (μ : pk ⟶ pf ⋙ pg) (ε : ef ⋙ eg ⟶ ek)
    (Af : TR ⋙ Pf ⟶ Ef ⋙ TS) (Ag : TS ⋙ Pg ⟶ Eg ⋙ TT)
    (hf : ∀ M : CR, Af.app (QR.obj M) ≫ TS.map (cf.app M) ≫ mS.app (ef.obj M) =
      Pf.map (mR.app M) ≫ df.app (tR.obj M) ≫ QS'.map (τf.app M))
    (hg : ∀ N : CS, Ag.app (QS.obj N) ≫ TT.map (cg.app N) ≫ mT.app (eg.obj N) =
      Pg.map (mS.app N) ≫ dg.app (tS.obj N) ≫ QT'.map (τg.app N))
    (hΦ : ∀ K : CR', Φ.app (QR'.obj K) ≫ Pg.map (df.app K) ≫ dg.app (pf.obj K) =
      dk.app K ≫ QT'.map (μ.app K))
    (hΨ : ∀ M : CR, Eg.map (cf.app M) ≫ cg.app (ef.obj M) ≫ QT.map (ε.app M) =
      Ψ.app (QR.obj M) ≫ ck.app M)
    (hdeg : ∀ M : CR, μ.app (tR.obj M) ≫ pg.map (τf.app M) ≫ τg.app (ef.obj M) ≫
      tT.map (ε.app M) = τk.app M)
    (M : CR) :
    Φ.app (TR.obj (QR.obj M)) ≫ Pg.map (Af.app (QR.obj M)) ≫ Ag.app (Ef.obj (QR.obj M)) ≫
        TT.map (Ψ.app (QR.obj M)) ≫ TT.map (ck.app M) ≫ mT.app (ek.obj M) =
      Pk.map (mR.app M) ≫ dk.app (tR.obj M) ≫ QT'.map (τk.app M) :=
  (whisker_eq _ (comp_app_comparisons mR mS mT df dg cf cg ck τf τg Ψ ε Af Ag hf hg hΨ M)).trans
    (comp_app_pullback mR df dg dk τf τg τk Φ μ.app ε hΦ hdeg M)

/-! ### The degreewise cocycle, for arbitrary categories and natural transformations -/

section Degreewise

variable {ι : Type*} {A A' B B' D D' : Type*} [Category* A] [Category* A'] [Category* B]
  [Category* B'] [Category* D] [Category* D'] [Limits.HasZeroMorphisms A]
  [Limits.HasZeroMorphisms A'] [Limits.HasZeroMorphisms B] [Limits.HasZeroMorphisms B']
  [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms D']
  {tR : A ⥤ A'} {tS : B ⥤ B'} {tT : D ⥤ D'} {pf : A' ⥤ B'} {pg : B' ⥤ D'} {pk : A' ⥤ D'}
  {ef : A ⥤ B} {eg : B ⥤ D} {ek : A ⥤ D}
  [tR.PreservesZeroMorphisms] [tS.PreservesZeroMorphisms] [tT.PreservesZeroMorphisms]
  [pf.PreservesZeroMorphisms] [pg.PreservesZeroMorphisms] [pk.PreservesZeroMorphisms]
  [ef.PreservesZeroMorphisms] [eg.PreservesZeroMorphisms] [ek.PreservesZeroMorphisms]

/-- **A cocycle of natural transformations passes to complexes.** If the square `μ`, `τf`, `τg`,
`ε`, `τk` commutes at every object, then it commutes at every complex, degreewise. -/
theorem mapHomologicalComplex_cocycle (c : ComplexShape ι)
    (μ : pk ⟶ pf ⋙ pg) (τf : tR ⋙ pf ⟶ ef ⋙ tS) (τg : tS ⋙ pg ⟶ eg ⋙ tT)
    (ε : ef ⋙ eg ⟶ ek) (τk : tR ⋙ pk ⟶ ek ⋙ tT)
    (h : ∀ N : A, μ.app (tR.obj N) ≫ pg.map (τf.app N) ≫ τg.app (ef.obj N) ≫
      tT.map (ε.app N) = τk.app N)
    (M : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex μ c).app ((tR.mapHomologicalComplex c).obj M) ≫
        (pg.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex τf c).app M) ≫
        (NatTrans.mapHomologicalComplex τg c).app ((ef.mapHomologicalComplex c).obj M) ≫
        (tT.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ε c).app M) =
      (NatTrans.mapHomologicalComplex τk c).app M :=
  HomologicalComplex.hom_ext _ _ fun n => h (M.X n)

end Degreewise

end StacksDraft.ComparisonSquare

namespace AlgebraicGeometry

variable (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T)

/-! ### The pinning equation with every whiskering evaluated -/

/-- **The comparison of derived extension of scalars, with the degreewise functor spelled out.**
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison`, typed with
codomain degreewise extension of scalars followed by the localisation functor rather than
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, which is not
syntactically that composite. -/
def StandardModel.extendScalarsComparison {R S : CommRingCat.{u}} (f : R ⟶ S) :
    DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⟶
      (ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} f.hom).comparison

/-- **The complex-level comparison of [Stacks, Tag 06YJ] along `Spec f`, at the scheme spelling.**
`AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison` for `Spec f`, with its derived
categories typed at `Scheme.Modules` rather than at `SheafOfModules (structureSheafRing _)`. -/
def StandardModel.specPullbackComplexComparison {R S : CommRingCat.{u}} (f : R ⟶ S) :
    DerivedCategory.Q ⋙ StandardModel.specDerivedPullback f ⟶
      (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  StandardModel.derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom

/-- Derived sheafification followed by derived pullback, read degreewise, at a complex: derived
pullback of the factorisation of derived sheafification through the localisation. -/
theorem StandardModel.tildeDerivedPullbackFactor_hom_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.tildeDerivedPullbackFactor R S f).hom.app M =
      (StandardModel.specDerivedPullback f).map
        ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) := by
  dsimp only [StandardModel.tildeDerivedPullbackFactor]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- The comparison from `Lf^* ∘ L~` to the degreewise `M^• ↦ f^*(M̃^•)`, at a complex: derived
pullback of the factorisation of derived sheafification, then the complex-level derived-pullback
comparison. -/
theorem StandardModel.tildeDerivedPullbackComparison_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.tildeDerivedPullbackComparison R S f).app M =
      (StandardModel.specDerivedPullback f).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) ≫
        (StandardModel.specPullbackComplexComparison f).app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  eq_whisker (StandardModel.tildeDerivedPullbackFactor_hom_app R S f M) _

/-- Degreewise extension of scalars followed by derived sheafification, at a complex: the
factorisation of derived sheafification through the localisation. -/
theorem StandardModel.extendScalarsTildeFactor_hom_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.extendScalarsTildeFactor R S f).hom.app M =
      (tilde.functor S).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  Category.id_comp _

/-- The comparison from `L~ ∘ L(S ⊗_R -)` to the degreewise `M^• ↦ (S ⊗_R M^•)~`, at a complex:
derived sheafification of the comparison of derived extension of scalars, then the factorisation
of derived sheafification through the localisation. The comparison of derived extension of
scalars is written as its ascription `AlgebraicGeometry.StandardModel.extendScalarsComparison`. -/
theorem StandardModel.extendScalarsTildeComparison_app_extendScalarsComparison
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.extendScalarsTildeComparison R S f).app M =
      (tilde.functor S).mapDerivedCategory.map
          ((StandardModel.extendScalarsComparison f).app M) ≫
        (tilde.functor S).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) :=
  (Category.id_comp _).trans (whisker_eq _ (StandardModel.extendScalarsTildeFactor_hom_app R S f M))

/-- The two degreewise functors agree after localisation, at a complex: the localisation of the
degreewise affine-pullback isomorphism of [Stacks, Tag 01I9]. -/
theorem StandardModel.tildePullbackComplexCompQIso_hom_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.tildePullbackComplexCompQIso R S f).hom.app M =
      DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app M) := by
  dsimp only [StandardModel.tildePullbackComplexCompQIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- **The normalisation of the affine comparison square, with every whiskering evaluated.** The
comparison at `Q.obj M`, followed by derived sheafification of the comparison of derived extension
of scalars and the factorisation of derived sheafification, is derived pullback of that
factorisation, then the complex-level derived-pullback comparison, then the localisation of the
degreewise isomorphism of [Stacks, Tag 01I9]. -/
theorem affinePullbackComparison_hom_app_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj M) ≫
        (tilde.functor S).mapDerivedCategory.map
          ((StandardModel.extendScalarsComparison f).app M) ≫
        (tilde.functor S).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
      (StandardModel.specDerivedPullback f).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) ≫
        (StandardModel.specPullbackComplexComparison f).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app M) := by
  rw [← StandardModel.extendScalarsTildeComparison_app_extendScalarsComparison,
    StandardModel.affinePullbackComparison_fac,
    StandardModel.tildeDerivedPullbackComparison_app,
    StandardModel.tildePullbackComplexCompQIso_hom_app]
  exact Category.assoc _ _ _

/-! ### The composition compatibility of [Stacks, Tag 01I9] on complexes -/

/-- The degreewise affine-pullback isomorphism of [Stacks, Tag 01I9] on complexes, in a single
degree: the isomorphism of [Stacks, Tag 01I9] at that term of the complex. -/
theorem tildePullbackComplexIso_hom_app_f
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((tildePullbackComplexIso R S f).hom.app M).f n =
      (pullbackTildeIso R S f).hom.app (M.X n) :=
  (Category.id_comp _).trans (Category.comp_id _)

/-- **The degreewise affine-pullback isomorphism of [Stacks, Tag 01I9] is the degreewise image of
the one on modules.** -/
theorem tildePullbackComplexIso_hom :
    (tildePullbackComplexIso R S f).hom =
      NatTrans.mapHomologicalComplex (pullbackTildeIso R S f).hom (ComplexShape.up ℤ) :=
  NatTrans.ext (funext fun M => HomologicalComplex.hom_ext _ _ fun n =>
    tildePullbackComplexIso_hom_app_f R S f M n)

/-- **Transposing the direction of a `pullbackCongr`.** For equal morphisms of schemes, the
inverse of the comparison of their pullback functors attached to one direction of the equality is
the forward morphism of the comparison attached to the other. -/
theorem pullbackCongr_symm_inv {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) :
    (Scheme.Modules.pullbackCongr h.symm).inv = (Scheme.Modules.pullbackCongr h).hom := by
  subst h
  rfl

/-- **The two degreewise composition isomorphisms for the pullback along `Spec (f ≫ g)` are
inverse.** `AlgebraicGeometry.StandardModel.specPullbackComp` is the inverse of
`AlgebraicGeometry.pullbackSpecMapCompIso`. -/
theorem specPullbackComp_inv :
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
          Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv =
      (pullbackSpecMapCompIso R S T f g).hom := by
  dsimp only [pullbackSpecMapCompIso]
  rw [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, pullbackCongr_symm_inv]

/-- `AlgebraicGeometry.specPullbackComp_inv` at an object. -/
theorem specPullbackComp_inv_app (N : (Spec R).Modules) :
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
          Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv.app N =
      (pullbackSpecMapCompIso R S T f g).hom.app N :=
  NatTrans.congr_app (specPullbackComp_inv R S T f g) N

/-- **[Stacks, Tag 01I9] composes**, with the composition isomorphism of the pullbacks spelled as
`AlgebraicGeometry.StandardModel.specPullbackComp`. -/
theorem pullbackTildeIso_hom_app_comp_specPullbackComp (N : ModuleCat.{u} R) :
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
          Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv.app ((tilde.functor R).obj N) ≫
        (Scheme.Modules.pullback (Spec.map g)).map ((pullbackTildeIso R S f).hom.app N) ≫
        (pullbackTildeIso S T g).hom.app ((ModuleCat.extendScalars.{u, u, u} f.hom).obj N) ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp.{u, u} f.hom g.hom).inv.app N) =
      (pullbackTildeIso R T (f ≫ g)).hom.app N := by
  rw [specPullbackComp_inv_app]
  exact (pullbackTildeIso_hom_app_comp R S T f g N).symm

/-- **[Stacks, Tag 01I9] composes, on complexes.** The degreewise affine-pullback isomorphism for
`f ≫ g`, read through the degreewise composition isomorphism of the pullbacks, is the one for `f`
pushed along `g^*`, then the one for `g`, then the associated sheaf of the inverse of
`ModuleCat.extendScalarsComp`. -/
theorem tildePullbackComplexIso_comp (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
            Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).symm
            (ComplexShape.up ℤ)).hom.app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((tildePullbackComplexIso R S f).hom.app M) ≫
        (tildePullbackComplexIso S T g).hom.app
          (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        ((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
            (ComplexShape.up ℤ)).inv.app M) =
      (tildePullbackComplexIso R T (f ≫ g)).hom.app M := by
  rw [tildePullbackComplexIso_hom R S f, tildePullbackComplexIso_hom S T g,
    tildePullbackComplexIso_hom R T (f ≫ g)]
  exact StacksDraft.ComparisonSquare.mapHomologicalComplex_cocycle (ComplexShape.up ℤ) _ _ _ _ _
    (pullbackTildeIso_hom_app_comp_specPullbackComp R S T f g) M

/-! ### The three composition laws -/

/-- **[Stacks, Tag 0D5S] for the complex-level comparison along `Spec f` and `Spec g`**, at the
factorisation `Spec g ≫ Spec f = Spec (f ≫ g)`, with every functor at the scheme spelling. -/
theorem StandardModel.specPullbackComplexComparison_comp
    (K : CochainComplex (Spec R).Modules ℤ) :
    (StandardModel.specDerivedPullbackComp R S T f g).inv.app (DerivedCategory.Q.obj K) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specPullbackComplexComparison f).app K) ≫
        (StandardModel.specPullbackComplexComparison g).app
          (((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      (StandardModel.specPullbackComplexComparison (f ≫ g)).app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
            Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).symm
            (ComplexShape.up ℤ)).hom.app K) :=
  (StandardModel.derivedPullbackComplexComparison_comp_schemeFactorIso (Spec.map g) (Spec.map f)
    (Spec.map (f ≫ g)) (Spec.map_comp f g).symm K).symm

/-- **[Stacks, Tag 06Y5] for the comparison of derived extension of scalars**, with the
degreewise scalar-tower isomorphism localised separately. -/
theorem totalDerivedExtensionScalarsComp_comparison_Q
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} g.hom).functor.map
          ((StandardModel.extendScalarsComparison f).app M) ≫
        (StandardModel.extendScalarsComparison g).app
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
              (ComplexShape.up ℤ)).inv.app M) =
      (totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app (DerivedCategory.Q.obj M) ≫
        (StandardModel.extendScalarsComparison (f ≫ g)).app M :=
  totalDerivedExtensionScalarsComp_comparison.{u, u} f.hom g.hom M

/-! ### The composition compatibility -/

/-- The whiskered composite of the two affine comparison squares, at an object of `D(R)`: the
composition isomorphism of [Stacks, Tag 0D5S], the square for `f` pushed along `Lg^*`, the square
for `g`, and derived sheafification of the composition isomorphism of [Stacks, Tag 06Y5]. -/
theorem affinePullbackComparisonComp_app (Y : DerivedCategory (ModuleCat.{u} R)) :
    (Functor.whiskerLeft (tilde.functor R).mapDerivedCategory
          (StandardModel.specDerivedPullbackComp R S T f g).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (StandardModel.affinePullbackComparison R S f).hom
          (StandardModel.specDerivedPullback g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} f.hom).functor
          (StandardModel.affinePullbackComparison S T g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom :
            (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
                (totalDerivedExtensionScalars.{u, u, u} g.hom).functor ⟶
              (totalDerivedExtensionScalars.{u, u, u} (f ≫ g).hom).functor)
          (tilde.functor T).mapDerivedCategory).app Y =
      (StandardModel.specDerivedPullbackComp R S T f g).inv.app
          ((tilde.functor R).mapDerivedCategory.obj Y) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.affinePullbackComparison R S f).hom.app Y) ≫
        (StandardModel.affinePullbackComparison S T g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj Y) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app Y) := by
  change (StandardModel.specDerivedPullbackComp R S T f g).inv.app
        ((tilde.functor R).mapDerivedCategory.obj Y) ≫
      𝟙 _ ≫
      (StandardModel.specDerivedPullback g).map
        ((StandardModel.affinePullbackComparison R S f).hom.app Y) ≫
      𝟙 _ ≫
      (StandardModel.affinePullbackComparison S T g).hom.app
        ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj Y) ≫
      𝟙 _ ≫
      (tilde.functor T).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app Y) = _
  simp only [Category.id_comp]

/-- **The comparison half of the chase, at the concrete data.** This is
`StacksDraft.ComparisonSquare.comp_app_comparisons` at the two affine comparison squares, the two
complex-level derived-pullback comparisons, the three comparisons of derived extension of scalars,
the two degreewise isomorphisms of [Stacks, Tag 01I9], the composition isomorphism of
[Stacks, Tag 06Y5] and the degreewise scalar-tower isomorphism. -/
theorem affinePullbackComparisonComp_comparisons_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.specDerivedPullback g).map
          ((StandardModel.affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj M)) ≫
        (StandardModel.affinePullbackComparison S T g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj
            (DerivedCategory.Q.obj M)) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app
            (DerivedCategory.Q.obj M)) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((StandardModel.extendScalarsComparison (f ≫ g)).app M) ≫
        (tilde.functor T).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
      (StandardModel.specDerivedPullback g).map
          ((StandardModel.specDerivedPullback f).map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specPullbackComplexComparison f).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          (DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app M)) ≫
        (StandardModel.specPullbackComplexComparison g).app
          (((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          ((tildePullbackComplexIso S T g).hom.app
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          (((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
              (ComplexShape.up ℤ)).inv.app M)) :=
  StacksDraft.ComparisonSquare.comp_app_comparisons
    (tilde.functor R).mapDerivedCategoryFactors.hom
    (tilde.functor S).mapDerivedCategoryFactors.hom
    (tilde.functor T).mapDerivedCategoryFactors.hom
    (StandardModel.specPullbackComplexComparison f)
    (StandardModel.specPullbackComplexComparison g)
    (StandardModel.extendScalarsComparison f) (StandardModel.extendScalarsComparison g)
    (StandardModel.extendScalarsComparison (f ≫ g))
    (tildePullbackComplexIso R S f).hom
    (tildePullbackComplexIso S T g).hom
    (totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
      (ComplexShape.up ℤ)).inv
    (StandardModel.affinePullbackComparison R S f).hom
    (StandardModel.affinePullbackComparison S T g).hom
    (affinePullbackComparison_hom_app_Q R S f) (affinePullbackComparison_hom_app_Q S T g)
    (totalDerivedExtensionScalarsComp_comparison_Q R S T f g) M

/-- **The derived-pullback squares of the chase, at the concrete data.** The three squares of
`StacksDraft.ComparisonSquare.comp_app_pullbackComp` at the concrete comparisons: the naturality
of the complex-level comparison for `Spec g` at the degreewise isomorphism of [Stacks, Tag 01I9]
for `f`, the naturality of the composition isomorphism of [Stacks, Tag 0D5S], and
`AlgebraicGeometry.StandardModel.specPullbackComplexComparison_comp`. -/
theorem affinePullbackComparisonComp_pullbackComp_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.specDerivedPullbackComp R S T f g).inv.app
          ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specDerivedPullback f).map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specPullbackComplexComparison f).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          (DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app M)) ≫
        (StandardModel.specPullbackComplexComparison g).app
          (((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) =
      (StandardModel.specDerivedPullback (f ≫ g)).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) ≫
        (StandardModel.specPullbackComplexComparison (f ≫ g)).app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
            Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).symm
            (ComplexShape.up ℤ)).hom.app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          (((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((tildePullbackComplexIso R S f).hom.app M)) := by
  have n3 := (StandardModel.specPullbackComplexComparison g).naturality
    ((tildePullbackComplexIso R S f).hom.app M)
  have n4 := (StandardModel.specDerivedPullbackComp R S T f g).inv.naturality
    ((tilde.functor R).mapDerivedCategoryFactors.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n3 n4
  rw [n3, ← reassoc_of% n4,
    reassoc_of% (StandardModel.specPullbackComplexComparison_comp R S T f g
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))]

/-- **The degreewise cocycle of the chase, at the concrete data.** This is
`StacksDraft.ComparisonSquare.comp_app_degreewise` at the three degreewise isomorphisms of
[Stacks, Tag 01I9] and the two degreewise composition isomorphisms. -/
theorem affinePullbackComparisonComp_degreewise_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
            Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).symm
            (ComplexShape.up ℤ)).hom.app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          (((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((tildePullbackComplexIso R S f).hom.app M)) ≫
        DerivedCategory.Q.map
          ((tildePullbackComplexIso S T g).hom.app
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          (((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
              (ComplexShape.up ℤ)).inv.app M)) =
      DerivedCategory.Q.map
        ((tildePullbackComplexIso R T (f ≫ g)).hom.app M) :=
  StacksDraft.ComparisonSquare.comp_app_degreewise
    (tildePullbackComplexIso R S f).hom
    (tildePullbackComplexIso S T g).hom
    (tildePullbackComplexIso R T (f ≫ g)).hom
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
      (ComplexShape.up ℤ)).inv
    (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
      Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).symm (ComplexShape.up ℤ)).hom.app
    (tildePullbackComplexIso_comp R S T f g) M

/-- **The pullback half of the chase, at the concrete data.** The derived-pullback squares of
`AlgebraicGeometry.affinePullbackComparisonComp_pullbackComp_Q` followed by the degreewise cocycle
of `AlgebraicGeometry.affinePullbackComparisonComp_degreewise_Q`. -/
theorem affinePullbackComparisonComp_pullback_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.specDerivedPullbackComp R S T f g).inv.app
          ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specDerivedPullback f).map
            ((tilde.functor R).mapDerivedCategoryFactors.hom.app M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.specPullbackComplexComparison f).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          (DerivedCategory.Q.map ((tildePullbackComplexIso R S f).hom.app M)) ≫
        (StandardModel.specPullbackComplexComparison g).app
          (((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          ((tildePullbackComplexIso S T g).hom.app
            (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Q.map
          (((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f.hom g.hom)
              (ComplexShape.up ℤ)).inv.app M)) =
      (StandardModel.specDerivedPullback (f ≫ g)).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) ≫
        (StandardModel.specPullbackComplexComparison (f ≫ g)).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Q.map
            ((tildePullbackComplexIso R T (f ≫ g)).hom.app M) := by
  rw [reassoc_of% (affinePullbackComparisonComp_pullbackComp_Q R S T f g M),
    affinePullbackComparisonComp_degreewise_Q R S T f g M]

/-- **The chase at the concrete data.** The whiskered composite of the two affine comparison
squares, normalised by the comparison of derived extension of scalars for `f ≫ g` and the
factorisation of derived sheafification, is the normalisation of the affine comparison square for
`f ≫ g`. -/
theorem affinePullbackComparison_comp_app_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.specDerivedPullbackComp R S T f g).inv.app
          ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj M)) ≫
        (StandardModel.affinePullbackComparison S T g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj
            (DerivedCategory.Q.obj M)) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app
            (DerivedCategory.Q.obj M)) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((StandardModel.extendScalarsComparison (f ≫ g)).app M) ≫
        (tilde.functor T).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
      (StandardModel.specDerivedPullback (f ≫ g)).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app M) ≫
        (StandardModel.specPullbackComplexComparison (f ≫ g)).app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Q.map
            ((tildePullbackComplexIso R T (f ≫ g)).hom.app M) :=
  (whisker_eq _ (affinePullbackComparisonComp_comparisons_Q R S T f g M)).trans
    (affinePullbackComparisonComp_pullback_Q R S T f g M)

/-- **The pinning equation for the whiskered composite.** At `Q.obj M` the affine comparison
square for `f ≫ g` and the whiskered composite of the squares for `f` and `g` agree after
composition with the comparison of [Stacks, Tag 06YJ] out of the localisation. -/
theorem affinePullbackComparison_comp_fac_Q (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (StandardModel.affinePullbackComparison R T (f ≫ g)).hom.app (DerivedCategory.Q.obj M) ≫
        (StandardModel.extendScalarsTildeComparison R T (f ≫ g)).app M =
      ((StandardModel.specDerivedPullbackComp R S T f g).inv.app
            ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
          (StandardModel.specDerivedPullback g).map
            ((StandardModel.affinePullbackComparison R S f).hom.app
              (DerivedCategory.Q.obj M)) ≫
          (StandardModel.affinePullbackComparison S T g).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj
              (DerivedCategory.Q.obj M)) ≫
          (tilde.functor T).mapDerivedCategory.map
            ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app
              (DerivedCategory.Q.obj M))) ≫
        (StandardModel.extendScalarsTildeComparison R T (f ≫ g)).app M := by
  rw [StandardModel.extendScalarsTildeComparison_app_extendScalarsComparison R T (f ≫ g) M,
    affinePullbackComparison_hom_app_Q R T (f ≫ g) M]
  simp only [Category.assoc]
  exact (affinePullbackComparison_comp_app_Q R S T f g M).symm

/-- **The affine comparison square composes, as natural transformations.** The square for `f ≫ g`
is the whiskered composite of the squares for `f` and `g`, read through the composition
isomorphism of [Stacks, Tag 0D5S] for derived pullback and the composition isomorphism of
[Stacks, Tag 06Y5] for derived extension of scalars. -/
theorem affinePullbackComparison_comp_hom :
    (StandardModel.affinePullbackComparison R T (f ≫ g)).hom =
      Functor.whiskerLeft (tilde.functor R).mapDerivedCategory
          (StandardModel.specDerivedPullbackComp R S T f g).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (StandardModel.affinePullbackComparison R S f).hom
          (StandardModel.specDerivedPullback g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} f.hom).functor
          (StandardModel.affinePullbackComparison S T g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom :
            (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
                (totalDerivedExtensionScalars.{u, u, u} g.hom).functor ⟶
              (totalDerivedExtensionScalars.{u, u, u} (f ≫ g).hom).functor)
          (tilde.functor T).mapDerivedCategory :=
  have := StandardModel.isLeftDerivedFunctor_extendScalarsTilde R T (f ≫ g)
  Functor.leftDerived_ext _ (StandardModel.extendScalarsTildeComparison R T (f ≫ g))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _
    (NatTrans.ext (funext fun M =>
      (affinePullbackComparison_comp_fac_Q R S T f g M).trans
        (eq_whisker (affinePullbackComparisonComp_app R S T f g (DerivedCategory.Q.obj M)) _).symm))

/-- **[Stacks, Tag 0FJX]: the affine comparison square composes.** For ring maps `f : R ⟶ S` and
`g : S ⟶ T`, the affine comparison square of [Stacks, Tag 08DW] part (2) for `f ≫ g`, evaluated
at an object of `D(R)`, is the square for `f` pushed along `Lg^*`, followed by the square for `g`,
read through the composition isomorphism of [Stacks, Tag 0D5S] for derived pullback and derived
sheafification of the composition isomorphism of [Stacks, Tag 06Y5] for derived extension of
scalars. -/
theorem affinePullbackComparison_comp (X : DerivedCategory (ModuleCat.{u} R)) :
    (StandardModel.affinePullbackComparison R T (f ≫ g)).hom.app X =
      ((Stacks.DerivedPullback.schemeFactorIso (Spec.map g) (Spec.map f)
            (Spec.map (f ≫ g)) (Spec.map_comp f g).symm).app
          ((tilde.functor R).mapDerivedCategory.obj X)).inv ≫
        (StandardModel.specDerivedPullback g).map
          ((StandardModel.affinePullbackComparison R S f).hom.app X) ≫
        (StandardModel.affinePullbackComparison S T g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj X) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app X) :=
  (NatTrans.congr_app (affinePullbackComparison_comp_hom R S T f g) X).trans
    (affinePullbackComparisonComp_app R S T f g X)

end AlgebraicGeometry

end
