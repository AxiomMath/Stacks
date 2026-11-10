module

public import StacksCore.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CobarFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.ExtSpectralSequenceFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.SpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descent spectral sequence of a finite surjection, functorially in the coefficient sheaf

Let `f : X ⟶ Y` be a finite surjective morphism of schemes, let `f_p : X_p ⟶ Y` be the structure
map of the `(p + 1)`-fold fibre product of `X` over `Y`, and let `F` be an abelian sheaf on the
small étale site of `Y`. [Stacks, Tag 09Z2] asserts an exact sequence
`0 → F → F_0 → F_1 → ⋯` with `F_p = f_{p,*}f_p^{-1}F`, a cohomological spectral sequence with

```
E_1^{p,q} = H^q_ét(X_p, f_p^{-1}F)
```

converging to `H^{p+q}_ét(Y, F)`, and — this is the clause this file supplies — that **the
spectral sequence is functorial in `F`**.

Functoriality is got by building every step of the construction as a functor of `F` instead of
as a choice made for one `F`. The resolution is the augmented cobar complex of the monad
`T = f_*f^{-1}`, which `Stacks.Cobar.cobarComplexFunctor` produces as a functor
`Ab(Y_ét) ⥤ Ch(Ab(Y_ét))` with a natural augmentation; the hyper-`Ext` spectral sequence of a
complex is `StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFunctor`, a
functor of the complex with its first page identified naturally. The composite is
`Stacks.EtaleCohomology.cechSpectralSequenceFunctor`, and the remaining work is to make the two
identifications of [Stacks, Tag 09Z2] natural as well:

* at the first page, the chain
  `E_1^{p,q}(F) ≅ Ext^q(ℤ, T^{p+1}F) ≅ H^q(Y, T^{p+1}F) ≅ H^q(Y, F_p) ≅ H^q(X_p, f_p^{-1}F)`,
  whose steps are the natural first-page isomorphism, the naturality of
  `Stacks.EtaleCohomology.sheafHAddEquivZExt` (proved here), the isomorphism of *functors*
  `Stacks.EtaleCohomology.cechSheafIterateIso`, and the comparison
  `H^q(Y, g_*G) ≅ H^q(W, G)` for an integral `g` in its functorial form
  `Stacks.Cohomology.BiggerSite.sheafCohomologyIso` ([Stacks, Tag 03YU]), which is available at
  these universes because the `Ext` universe `u + 1` is the morphism universe of the sites;
* at the abutment, the filtration of
  `StacksDraft.ExtSpectralSequence.hyperExtFiltration` carried along the natural isomorphism
  `Ext^n(ℤ, cobar F) ≅ H^n(Y, F)`, which is natural because the cobar augmentation is a natural
  transformation and quasi-isomorphism at every `F`.

## Main definitions

* `Stacks.EtaleCohomology.sheafHFunctor` — étale cohomology in a fixed degree as a functor of the
  coefficient sheaf.
* `Stacks.EtaleCohomology.cechSpectralSequenceFunctor` — **the descent spectral sequence as a
  functor of `F`.**
* `Stacks.EtaleCohomology.cechAbutmentFiltration` — the filtration of `H^n(Y, F)` it converges
  through.

## Main results

* `Stacks.EtaleCohomology.sheafHNatIsoZExt` — étale cohomology is the `ℤ`-graded `Ext` the
  spectral-sequence machinery uses, *naturally in the sheaf*.
* `Stacks.EtaleCohomology.sheafHPushforwardNatIso` — for an integral morphism `g`,
  `H^q(W, ·) ≅ H^q(Y, g_*·)`, naturally.
* `Stacks.EtaleCohomology.cechSpectralSequenceFirstPageNatIso` — **the first page is
  `H^q(X_p, f_p^{-1}F)` naturally in `F`.**
* `Stacks.EtaleCohomology.exists_cechAbutmentFiltration_le` — **the abutment filtration is
  natural in `F`.**
* `Stacks.EtaleCohomology.exists_cechSheafSpectralSequence_functorial` — **[Stacks, Tag 09Z2]**:
  all three assertions of the tag.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 0AVI](https://stacks.math.columbia.edu/tag/0AVI)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open StacksDraft.ExtSpectralSequenceFunctorial

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtaleTopology
attribute [local instance] enoughInjectives_sheaf_smallEtaleTopology
attribute [local instance] hasDerivedCategory_sheaf_smallEtaleTopology

/-! ### Étale cohomology as a functor of the coefficient sheaf -/

/-- **Étale cohomology in degree `q` as a functor of the coefficient sheaf.** It is Mathlib's
`CategoryTheory.Sheaf.functorH` for the small étale topology, with the coefficient and `Ext`
universes pinned to the convention of this namespace; its value at a sheaf is
`CategoryTheory.Sheaf.H` and its value at a morphism is `CategoryTheory.Sheaf.H.map`. -/
@[sga "4 VII 1.3"]
public abbrev sheafHFunctor (Y : Scheme.{u}) (q : ℕ) :
    Sheaf (smallEtaleTopology Y) Ab.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH (smallEtaleTopology Y) q

/-- The value of `Stacks.EtaleCohomology.sheafHFunctor` is the étale cohomology group it is named
for. -/
public lemma sheafHFunctor_obj (Y : Scheme.{u}) (q : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (sheafHFunctor Y q).obj F = AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} F q) :=
  rfl

/-- The value of `Stacks.EtaleCohomology.sheafHFunctor` at a morphism is
`CategoryTheory.Sheaf.H.map`. -/
public lemma sheafHFunctor_map (Y : Scheme.{u}) (q : ℕ)
    {F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : F ⟶ G)
    (α : Sheaf.H.{u + 1, u + 1} F q) :
    (sheafHFunctor Y q).map φ α = Sheaf.H.map.{u + 1, u + 1} φ q α :=
  rfl

/-- **The `ℤ`-graded `Ext` out of the constant sheaf `ℤ` in degree `q`, as a functor of the
coefficient sheaf.** This is the group the hyper-`Ext` spectral sequence of [Stacks, Tag 0AVI] is
stated with; `Stacks.EtaleCohomology.sheafHNatIsoZExt` identifies it with étale cohomology. -/
public def zExtConstZFunctor (Y : Scheme.{u}) (q : ℤ) :
    Sheaf (smallEtaleTopology Y) Ab.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0 ⋙
    (preadditiveCoyoneda.obj (Opposite.op
      ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj
        (constZ Y)))).shift q

/-- Degree `p` of a complex followed by `Stacks.EtaleCohomology.zExtConstZFunctor` is the
first-page functor of the hyper-`Ext` spectral sequence of [Stacks, Tag 0AVI]. -/
public lemma zExtXFunctor_eq (Y : Scheme.{u}) (p q : ℤ) :
    zExtXFunctor (constZ Y) p q =
      HomologicalComplex.eval (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (ComplexShape.up ℤ) p ⋙
        zExtConstZFunctor Y q :=
  rfl

/-- **Naturality of the identification of étale cohomology with `ℤ`-graded `Ext`.** For
`φ : F ⟶ G` the map `H^q(Y, φ)` becomes postcomposition with `φ`, placed in degree zero and
shifted by `q`, which is the action of
`Stacks.EtaleCohomology.zExtConstZFunctor` on `φ`. This is naturality of Mathlib's
`CategoryTheory.Abelian.Ext.homAddEquiv`, which holds because the map on `Ext` is composition
with `CategoryTheory.Abelian.Ext.mk₀ φ`, whose underlying morphism in the derived category is
`φ` in degree zero. -/
public lemma sheafHAddEquivZExt_naturality {Y : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : F ⟶ G) (q : ℕ)
    (α : Sheaf.H.{u + 1, u + 1} F q) :
    sheafHAddEquivZExt G q (Sheaf.H.map.{u + 1, u + 1} φ q α) =
      sheafHAddEquivZExt F q α ≫
        ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).map
          φ)⟦(q : ℤ)⟧' := by
  change (Abelian.Ext.comp α (Abelian.Ext.mk₀ φ) (add_zero q)).hom =
    Abelian.Ext.hom α ≫
      ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).map
        φ)⟦(q : ℤ)⟧'
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom]
  exact ShiftedHom.comp_mk₀ _ _ _ _

/-- **Étale cohomology is the `ℤ`-graded `Ext` out of the constant sheaf `ℤ`, naturally in the
coefficient sheaf.** The components are `Stacks.EtaleCohomology.sheafHAddEquivZExt` and the
naturality is `Stacks.EtaleCohomology.sheafHAddEquivZExt_naturality`. -/
public def sheafHNatIsoZExt (Y : Scheme.{u}) (q : ℕ) :
    sheafHFunctor Y q ≅ zExtConstZFunctor Y (q : ℤ) :=
  NatIso.ofComponents (fun F => (sheafHAddEquivZExt F q).toAddCommGrpIso)
    (fun {_ _} φ => by
      ext α
      exact sheafHAddEquivZExt_naturality φ q α)

/-! ### Direct image along an integral morphism, functorially -/

/-- **Direct image along an integral morphism does not change global étale cohomology, naturally
in the sheaf.** This is `Stacks.Cohomology.BiggerSite.sheafCohomologyIso` — [Stacks, Tag 03YU] in
its functorial form, available here because the `Ext` universe `u + 1` *is* the morphism universe
of the two small étale sites — for the morphism of sites induced by `g`. The two instances it
asks for are that direct image along an integral morphism is right exact (it is exact, by
[Stacks, Tag 04C2]) and that it preserves injectives (it is a right adjoint of an exact
functor); they are the ones `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, the
objectwise form of the same comparison, is built with. -/
public def sheafHPushforwardNatIso {W Y : Scheme.{u}} (g : W ⟶ Y) [IsIntegralHom g] (q : ℕ) :
    sheafHFunctor W q ≅ smallEtalePushforwardAb g ⋙ sheafHFunctor Y q :=
  let : PreservesFiniteColimits ((smallEtaleBaseChange g).sheafPushforwardContinuous
      Ab.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology W)) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom g)).2
  let : ((smallEtaleBaseChange g).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology W)).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects g
  (Stacks.Cohomology.BiggerSite.sheafCohomologyIso (smallEtaleTopology Y)
    (smallEtaleTopology W) (smallEtaleBaseChange g) terminalIsTerminal
    (isTerminalSmallEtaleBaseChangeObj g terminalIsTerminal) rfl q).symm

/-! ### The spectral sequence as a functor -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The augmented cobar complex of the monad `T = f_*f^{-1}` on `F`: the resolution
`0 → F → F_0 → F_1 → ⋯` of [Stacks, Tag 09Z2] read as a cochain complex in the nonnegative
degrees. -/
public abbrev cechCobarComplex (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ :=
  (Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f)).obj F

/-- **The descent spectral sequence of [Stacks, Tag 09Z2], as a functor of the coefficient
sheaf.** It is the hyper-`Ext` spectral sequence of [Stacks, Tag 0AVI] out of the constant sheaf
`ℤ`, applied to the augmented cobar complex of the monad `f_*f^{-1}`; both halves are functors,
so a morphism `F ⟶ G` of abelian sheaves induces a morphism of spectral sequences. -/
public def cechSpectralSequenceFunctor :
    Sheaf (smallEtaleTopology Y) Ab.{u + 1} ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 :=
  Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f) ⋙
    extComplexSpectralSequenceFunctor (constZ Y)

/-- The first page of the hyper-`Ext` spectral sequence of the cobar complex is
`Ext^q(ℤ, (cobar F)^p)`, naturally in `F`: this is the natural first-page identification of
[Stacks, Tag 0AVI]. -/
public def firstPageStep₁ (p q : ℕ) :
    cechSpectralSequenceFunctor f ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u + 1} _ 1 1 (le_refl 1) ⋙
          HomologicalComplex.eval AddCommGrpCat.{u + 1} _ ((p : ℤ), (q : ℤ)) ≅
      Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f) ⋙
        HomologicalComplex.eval (Sheaf (smallEtaleTopology Y) Ab.{u + 1})
            (ComplexShape.up ℤ) (p : ℤ) ⋙
          zExtConstZFunctor Y (q : ℤ) :=
  Functor.isoWhiskerLeft (Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f))
    (extComplexSpectralSequenceFirstPageNatIso (constZ Y) (p : ℤ) (q : ℤ))

/-- Degree `p` of the cobar complex is the `(p+1)`-st power of the monad `f_*f^{-1}`, naturally
in `F`: this is `Stacks.Cobar.cobarComplexFunctorXIso`. -/
public def firstPageStep₂ (p q : ℕ) :
    Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f) ⋙
        HomologicalComplex.eval (Sheaf (smallEtaleTopology Y) Ab.{u + 1})
            (ComplexShape.up ℤ) (p : ℤ) ⋙
          zExtConstZFunctor Y (q : ℤ) ≅
      (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (p + 1) ⋙
        zExtConstZFunctor Y (q : ℤ) :=
  Functor.isoWhiskerRight (Stacks.Cobar.cobarComplexFunctorXIso (smallEtaleAdjunctionAb f) p)
    (zExtConstZFunctor Y (q : ℤ))

/-- The `ℤ`-graded `Ext` out of the constant sheaf `ℤ` is étale cohomology, naturally: this is
`Stacks.EtaleCohomology.sheafHNatIsoZExt`, the first of the two naturalities the functoriality
clause of [Stacks, Tag 09Z2] needs. -/
public def firstPageStep₃ (p q : ℕ) :
    (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (p + 1) ⋙
        zExtConstZFunctor Y (q : ℤ) ≅
      (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (p + 1) ⋙
        sheafHFunctor Y q :=
  Functor.isoWhiskerLeft
    ((Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (p + 1))
    (sheafHNatIsoZExt Y q).symm

/-- The `(p+1)`-st power of the monad is the `p`-th Čech level: this is the isomorphism of
functors `Stacks.EtaleCohomology.cechSheafIterateIso`. -/
public def firstPageStep₄ [IsFinite f] (p q : ℕ) :
    (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (p + 1) ⋙
        sheafHFunctor Y q ≅
      (smallEtalePullbackAb (cechProjection f p) ⋙
        smallEtalePushforwardAb (cechProjection f p)) ⋙ sheafHFunctor Y q :=
  Functor.isoWhiskerRight (cechSheafIterateIso f p).symm (sheafHFunctor Y q)

/-- Direct image along the finite, hence integral, morphism `f_p` does not change global étale
cohomology, naturally in the sheaf: this is
`Stacks.EtaleCohomology.sheafHPushforwardNatIso`, the second of the two naturalities the
functoriality clause of [Stacks, Tag 09Z2] needs at the first page. -/
public def firstPageStep₅ [IsFinite f] (p q : ℕ) :
    (smallEtalePullbackAb (cechProjection f p) ⋙
          smallEtalePushforwardAb (cechProjection f p)) ⋙ sheafHFunctor Y q ≅
      smallEtalePullbackAb (cechProjection f p) ⋙ sheafHFunctor (cechScheme f p) q :=
  Functor.isoWhiskerLeft (smallEtalePullbackAb (cechProjection f p))
    (sheafHPushforwardNatIso (cechProjection f p) q).symm

/-- **The first page of the descent spectral sequence is `H^q(X_p, f_p^{-1}F)`, naturally in
`F`.** The five steps are: the natural first-page identification of [Stacks, Tag 0AVI]; the
degreewise identification of the cobar complex with the iterates of the monad; the naturality of
`Stacks.EtaleCohomology.sheafHAddEquivZExt`; the isomorphism of functors
`Stacks.EtaleCohomology.cechSheafIterateIso`, which says that the `p`-th Čech level computes the
`(p+1)`-st power of the monad; and the naturality of the comparison
`H^q(Y, f_{p,*}f_p^{-1}F) ≅ H^q(X_p, f_p^{-1}F)` for the finite, hence integral, morphism
`f_p`. -/
@[sga "4 Vbis 2.5.5" "partial"]
public def cechSpectralSequenceFirstPageNatIso [IsFinite f] (p q : ℕ) :
    cechSpectralSequenceFunctor f ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u + 1} _ 1 1 (le_refl 1) ⋙
          HomologicalComplex.eval AddCommGrpCat.{u + 1} _ ((p : ℤ), (q : ℤ)) ≅
      smallEtalePullbackAb (cechProjection f p) ⋙ sheafHFunctor (cechScheme f p) q :=
  firstPageStep₁ f p q ≪≫ firstPageStep₂ f p q ≪≫ firstPageStep₃ f p q ≪≫
    firstPageStep₄ f p q ≪≫ firstPageStep₅ f p q

/-! ### The abutment -/

section Abutment

variable [Surjective f]

/-- Inverse image along `f` reflects exactness of short complexes of abelian étale sheaves, for
`f` surjective. This is the hypothesis `Stacks.Cobar.quasiIso_cobarAugmentation` asks for. -/
public lemma cobar_hrefl :
    ∀ S : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
      (S.map (smallEtalePullbackAb f)).Exact → S.Exact :=
  fun S hS => exact_of_exact_map_smallEtalePullbackAb f S hS

/-- Inverse image along `f` reflects monomorphisms of abelian étale sheaves, for `f` surjective.
This is the other hypothesis `Stacks.Cobar.quasiIso_cobarAugmentation` asks for. -/
public lemma cobar_hmono :
    ∀ {P Q : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : P ⟶ Q),
      Mono ((smallEtalePullbackAb f).map φ) → Mono φ :=
  fun φ hφ => mono_of_mono_smallEtalePullbackAb_map f φ hφ

/-- **The cobar resolution computes the coefficient sheaf in the derived category, naturally in
the sheaf.** The augmentation `F[0] ⟶ cobar F` is a transformation of functors
(`Stacks.Cobar.cobarAugmentation`) which is a quasi-isomorphism at every `F`
(`Stacks.Cobar.quasiIso_cobarAugmentation`, whose two hypotheses hold because `f` is
surjective), so it becomes an isomorphism of functors to the derived category. -/
public def cobarQNatIso :
    DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0 ≅
      Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun F => by
      have : IsIso (DerivedCategory.Q.map
          ((Stacks.Cobar.cobarAugmentation (smallEtaleAdjunctionAb f)).app F)) := by
        rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
        exact Stacks.Cobar.quasiIso_cobarAugmentation (smallEtaleAdjunctionAb f)
          (cobar_hrefl f) (cobar_hmono f) F
      exact asIso (DerivedCategory.Q.map
        ((Stacks.Cobar.cobarAugmentation (smallEtaleAdjunctionAb f)).app F)))
    (fun {F G} φ => by
      change DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) ≫
          DerivedCategory.Q.map
            ((Stacks.Cobar.cobarAugmentation (smallEtaleAdjunctionAb f)).app G) =
        DerivedCategory.Q.map
            ((Stacks.Cobar.cobarAugmentation (smallEtaleAdjunctionAb f)).app F) ≫
          DerivedCategory.Q.map
            ((Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f)).map φ)
      rw [← Functor.map_comp, ← Functor.map_comp,
        (Stacks.Cobar.cobarAugmentation (smallEtaleAdjunctionAb f)).naturality φ])

/-- **The abutment of the descent spectral sequence is the étale cohomology of `F`, naturally in
`F`.** The hyper-`Ext` spectral sequence of the cobar complex abuts to `Ext^n(ℤ, cobar F)`; the
cobar augmentation identifies that with `Ext^n(ℤ, F[0])`, which is `H^n(Y, F)` by
`Stacks.EtaleCohomology.sheafHNatIsoZExt`. Both steps are natural in `F`. -/
public def cechAbutmentNatIso (n : ℕ) :
    Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f) ⋙
        zExtAbutmentFunctor (constZ Y) (n : ℤ) ≅ sheafHFunctor Y n :=
  Functor.isoWhiskerRight (cobarQNatIso f).symm
      ((preadditiveCoyoneda.obj (Opposite.op
        ((DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj
          (constZ Y)))).shift (n : ℤ)) ≪≫
    (sheafHNatIsoZExt Y n).symm

/-- The component of the identification of the abutment is an isomorphism. -/
public lemma isIso_cechAbutmentNatIso_hom_app (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    IsIso ((cechAbutmentNatIso f n).hom.app F) :=
  (Iso.app (cechAbutmentNatIso f n) F).isIso_hom

/-- The component of the identification of the abutment is a monomorphism, being an
isomorphism. -/
public lemma mono_cechAbutmentNatIso_hom_app (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    Mono ((cechAbutmentNatIso f n).hom.app F) :=
  have := isIso_cechAbutmentNatIso_hom_app f n F
  IsIso.mono_of_iso _

/-- **The filtration of `H^n(Y, F)` the descent spectral sequence converges through.** It is the
filtration by the images of the stupid truncations of the cobar complex,
`StacksDraft.ExtSpectralSequenceFunctorial.zExtAbutmentFiltration`, carried to `H^n(Y, F)` along
`Stacks.EtaleCohomology.cechAbutmentNatIso`. -/
public def cechAbutmentFiltration (p : ℤ) (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    Subobject ((sheafHFunctor Y n).obj F) :=
  have := mono_cechAbutmentNatIso_hom_app f n F
  Subobject.mk ((zExtAbutmentFiltration (constZ Y) (cechCobarComplex f F) p (n : ℤ)).arrow ≫
    (cechAbutmentNatIso f n).hom.app F)

/-- **A step of the transported filtration is the image of the corresponding step upstairs.**
This is the form in which the filtration is used: `Stacks.Subobject.exists` needs no
monomorphism hypothesis, so rewriting with it is what keeps the proofs below free of
instance arguments that depend on the subobject. -/
public lemma cechAbutmentFiltration_eq_exists (p : ℤ) (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    cechAbutmentFiltration f p n F =
      (Subobject.«exists» ((cechAbutmentNatIso f n).hom.app F)).obj
        (zExtAbutmentFiltration (constZ Y) (cechCobarComplex f F) p (n : ℤ)) := by
  have := mono_cechAbutmentNatIso_hom_app f n F
  rw [Subobject.exists_eq_imageSubobject, imageSubobject_mono]
  rfl

/-- **The filtration of the abutment is decreasing.** -/
public lemma cechAbutmentFiltration_antitone (p p' : ℤ) (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (h : p ≤ p') :
    cechAbutmentFiltration f p' n F ≤ cechAbutmentFiltration f p n F := by
  rw [cechAbutmentFiltration_eq_exists, cechAbutmentFiltration_eq_exists]
  exact (Subobject.«exists» ((cechAbutmentNatIso f n).hom.app F)).monotone
    (zExtAbutmentFiltration_antitone (constZ Y) (cechCobarComplex f F) (n : ℤ) h)

/-- **The filtration of the abutment is natural in `F`.** A morphism `φ : F ⟶ G` carries
`Fil^p H^n(Y, F)` into `Fil^p H^n(Y, G)`: the identification of the abutment is natural, and
upstairs the statement is
`StacksDraft.ExtSpectralSequenceFunctorial.exists_zExtAbutmentFiltration_le` for the cobar
complex of `φ`. -/
public lemma exists_cechAbutmentFiltration_le (p : ℤ) (n : ℕ)
    (F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (φ : F ⟶ G) :
    (Subobject.«exists» ((sheafHFunctor Y n).map φ)).obj (cechAbutmentFiltration f p n F) ≤
      cechAbutmentFiltration f p n G := by
  rw [cechAbutmentFiltration_eq_exists, cechAbutmentFiltration_eq_exists,
    ← Subobject.exists_comp, ← (cechAbutmentNatIso f n).hom.naturality φ, Subobject.exists_comp]
  exact (Subobject.«exists» ((cechAbutmentNatIso f n).hom.app G)).monotone
    (exists_zExtAbutmentFiltration_le
      ((Stacks.Cobar.cobarComplexFunctor (smallEtaleAdjunctionAb f)).map φ) (constZ Y) p (n : ℤ))

/-- **The filtration of the abutment is finite**: it is everything in filtration degree `0` and
zero in filtration degrees above `n`, the cobar complex being concentrated in the nonnegative
degrees. -/
public lemma cechAbutmentFiltration_finite (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    ∃ s t : ℤ, s ≤ t ∧ cechAbutmentFiltration f s n F = ⊤ ∧
      cechAbutmentFiltration f t n F = ⊥ := by
  have := isIso_cechAbutmentNatIso_hom_app f n F
  obtain ⟨s, t, hst, hs, ht⟩ := zExtAbutmentFiltration_finite (constZ Y)
    (cechCobarComplex f F) ⟨0, inferInstance⟩ (n : ℤ)
  refine ⟨s, t, hst, ?_, ?_⟩
  · rw [cechAbutmentFiltration_eq_exists, hs]
    exact Subobject.exists_obj_top_of_isIso _
  · rw [cechAbutmentFiltration_eq_exists, ht, Subobject.exists_eq_imageSubobject,
      Subobject.bot_arrow, zero_comp, imageSubobject_zero]

/-- **The descent spectral sequence converges to the étale cohomology of `F`.** In every
bidegree all sufficiently late pages have vanishing incoming and outgoing differentials and are
isomorphic to the corresponding graded piece of
`Stacks.EtaleCohomology.cechAbutmentFiltration`. This is the convergence of [Stacks, Tag 0AVI]
for the cobar complex — which is literally the spectral sequence
`Stacks.EtaleCohomology.cechSpectralSequenceFunctor` produces, by
`StacksDraft.ExtSpectralSequenceFunctorial.extComplexSpectralSequenceFunctor_obj` — with the
graded pieces carried along the identification of the abutment. -/
public theorem cechSpectralSequence_convergence (p q : ℤ) (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (hn : p + q = (n : ℤ)) :
    ∃ r₀ : ℤ, 1 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
      (((cechSpectralSequenceFunctor f).obj F).page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
        (((cechSpectralSequenceFunctor f).obj F).page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
          Nonempty ((((cechSpectralSequenceFunctor f).obj F).page r hr).X (p, q) ≅
            cokernel (Subobject.ofLE (cechAbutmentFiltration f (p + 1) n F)
              (cechAbutmentFiltration f p n F)
              (cechAbutmentFiltration_antitone f p (p + 1) n F (by omega)))) := by
  obtain ⟨r₁, hr₁, hd⟩ :=
    StacksDraft.ExtSpectralSequence.hyperExtSpectralSequence_eventually_d_eq_zero
      (cechCobarComplex f F) (constZ Y) ⟨0, inferInstance⟩ p q
  have key : ∀ m : ℤ, m = (n : ℤ) →
      ∀ (h₀ : zExtAbutmentFiltration (constZ Y) (cechCobarComplex f F) (p + 1) m ≤
          zExtAbutmentFiltration (constZ Y) (cechCobarComplex f F) p m)
        (h₁ : cechAbutmentFiltration f (p + 1) n F ≤ cechAbutmentFiltration f p n F),
        Nonempty (cokernel (Subobject.ofLE _ _ h₀) ≅ cokernel (Subobject.ofLE _ _ h₁)) := by
    intro m hm h₀ _
    subst hm
    exact ⟨cokernelMkIso (Iso.app (cechAbutmentNatIso f n) F) _ _ h₀⟩
  refine ⟨max r₁ (max (q + 2) (p + 1)), by omega, fun r hr hle => ?_⟩
  exact ⟨(hd r hr (by omega)).1, (hd r hr (by omega)).2,
    ⟨zExtAbutmentPageIsoFiltration (constZ Y) (cechCobarComplex f F) 0 p q r hr
        (by omega) (by omega) ≪≫ (key (p + q) hn _ _).some⟩⟩

end Abutment

/-! ### The tag -/

/-- **[Stacks, Tag 09Z2].** Let `f : X ⟶ Y` be a surjective finite morphism of schemes, let
`f_n : X_n ⟶ Y` be the structure map of the `(n + 1)`-fold fibre product of `X` over `Y`, and for
an abelian sheaf `F` on the small étale site of `Y` put `F_n = f_{n,*}f_n^{-1}F`. Then:

* there is an exact sequence `0 → F → F_0 → F_1 → F_2 → ⋯` on `Y_étale`, with augmentation the
  canonical map `F ⟶ f_*f^{-1}F`;
* there is a cohomological spectral sequence with
  `E_1^{p,q} = H^q_étale(X_p, f_p^{-1}F)` converging to `H^{p+q}(Y_étale, F)`, convergence
  meaning that each `H^n(Y_étale, F)` carries a finite decreasing filtration `Fil` whose graded
  pieces are the stable terms of the spectral sequence;
* **this spectral sequence is functorial in `F`**: it is produced by a *functor* `E` of `F`, the
  first-page identification is an isomorphism of functors of `F`, and the filtration of the
  abutment is carried into itself by the map a morphism `F ⟶ G` induces on cohomology.

The exact sequence is `Stacks.EtaleCohomology.exists_exact_cechSheafSequence`; the functor is
`Stacks.EtaleCohomology.cechSpectralSequenceFunctor`, the augmented cobar complex of the monad
`f_*f^{-1}` followed by the hyper-`Ext` spectral sequence of [Stacks, Tag 0AVI]. -/
@[stacks 09Z2]
public theorem exists_cechSheafSpectralSequence_functorial [IsFinite f] [Surjective f] :
    (∀ F : Sheaf (smallEtaleTopology Y) Ab.{u + 1},
        ∃ (d : ∀ n : ℕ, cechSheaf f F n ⟶ cechSheaf f F (n + 1))
          (haug : cechAug f F ≫ d 0 = 0) (hdd : ∀ n : ℕ, d n ≫ d (n + 1) = 0),
          Mono (cechAug f F) ∧ (ShortComplex.mk _ _ haug).Exact ∧
            ∀ n : ℕ, (ShortComplex.mk _ _ (hdd n)).Exact) ∧
      ∃ E : Sheaf (smallEtaleTopology Y) Ab.{u + 1} ⥤
          CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1,
        (∀ p q : ℕ, Nonempty (E ⋙
            CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u + 1} _ 1 1 (le_refl 1) ⋙
              HomologicalComplex.eval AddCommGrpCat.{u + 1} _ ((p : ℤ), (q : ℤ)) ≅
            smallEtalePullbackAb (cechProjection f p) ⋙
              sheafHFunctor (cechScheme f p) q)) ∧
          ∃ (Fil : ∀ (_p : ℤ) (n : ℕ) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
                Subobject ((sheafHFunctor Y n).obj F))
            (hFil : ∀ (p p' : ℤ) (n : ℕ) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
                p ≤ p' → Fil p' n F ≤ Fil p n F),
            (∀ (p : ℤ) (n : ℕ) (F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (φ : F ⟶ G),
                (Subobject.«exists» ((sheafHFunctor Y n).map φ)).obj (Fil p n F) ≤
                  Fil p n G) ∧
              (∀ (n : ℕ) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
                  ∃ s t : ℤ, s ≤ t ∧ Fil s n F = ⊤ ∧ Fil t n F = ⊥) ∧
                ∀ (p q : ℤ) (n : ℕ) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}),
                  p + q = (n : ℤ) → ∃ r₀ : ℤ, 1 ≤ r₀ ∧
                    ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
                      ((E.obj F).page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
                        ((E.obj F).page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
                          Nonempty (((E.obj F).page r hr).X (p, q) ≅
                            cokernel (Subobject.ofLE (Fil (p + 1) n F) (Fil p n F)
                              (hFil p (p + 1) n F (by omega)))) :=
  ⟨fun F => exists_exact_cechSheafSequence f F, cechSpectralSequenceFunctor f,
    fun p q => ⟨cechSpectralSequenceFirstPageNatIso f p q⟩,
    cechAbutmentFiltration f,
    fun p p' n F h => cechAbutmentFiltration_antitone f p p' n F h,
    fun p n F G φ => exists_cechAbutmentFiltration_le f p n F G φ,
    fun n F => cechAbutmentFiltration_finite f n F,
    fun p q n F hn => cechSpectralSequence_convergence f p q n F hn⟩

end Stacks.EtaleCohomology

end
