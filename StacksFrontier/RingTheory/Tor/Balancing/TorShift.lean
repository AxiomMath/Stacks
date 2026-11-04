module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# `Tor` in degrees zero and one, and the dimension shift on the `Tor` side

The exactness instances for `tensorLeft` and `tensorRight`, the factorization of the
comparison through `Tor'`, the dimension-shift isomorphism `Tor_iso_Tor'.torShift` coming
from the long exact sequence of `Tor` in the first variable, and the description of `Tor_1`
as the common kernel functor `Tor_iso_Tor'.oneKer`.

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

universe u

/-!
## Balancing of `Tor` over a commutative ring

For a commutative ring `R` and every `i : ℕ` the two bifunctors

  `Mod_R × Mod_R → Mod_R`,  `(M, N) ↦ Tor_i^R(M, N)`

and

  `Mod_R × Mod_R → Mod_R`,  `(M, N) ↦ Tor_i^R(N, M)`

are canonically isomorphic: there is a natural isomorphism
`η_{M,N} : Tor_i^R(M, N) ≅ Tor_i^R(N, M)` of `R`-modules, natural in the pair `(M, N)`, so
that for all module maps `φ : M₁ ⟶ M₂` and `ψ : N₁ ⟶ N₂` the evident square commutes.

### Conventions

* We work in the category `ModuleCat R` of `R`-modules. For a commutative ring `R` this is
  an abelian monoidal category (monoidal product `⊗_R`) with enough projectives, so
  Mathlib's `CategoryTheory.Tor (ModuleCat R) i : C ⥤ C ⥤ C` is defined.
* The Stacks project defines `Tor_i^R(M, N)` by resolving the *first* argument by a free
  resolution and tensoring with `N`, i.e. `Tor_i^R(M, N) = H_i(F_• ⊗_R N)`. Over
  `ModuleCat R` free modules are projective and projective resolutions compute the same
  homology, so Mathlib's derived-functor `Tor` realizes that definition.
* A bifunctor `Mod_R × Mod_R → Mod_R` is written in curried form as a functor `C ⥤ C ⥤ C`,
  and swapping its two arguments is `Functor.flip`. Thus the swap bifunctor
  `(M, N) ↦ Tor_i^R(N, M)` is `(Tor (ModuleCat R) i).flip`.
* "Canonically isomorphic" means isomorphic as functors: a term of type `F ≅ G` in
  `C ⥤ (C ⥤ C)` is a family of isomorphisms compatible with all morphisms in *both*
  variables simultaneously, which is the naturality asserted by the statement.
* The comparison is canonical only up to sign (Stacks Tag 00M4): the induced self-map of
  `Tor_i^R(M, M)` need not be the identity, and no sign normalization is imposed.

### Implementation notes

`Tor_iso_Tor'` is assembled by dimension-shifting induction on `i`, recursing on the first
syzygy `K = ker (Projective.π M)`. In degree `0` both sides are `M ⊗ -`
(`Tor_iso_Tor'.zeroIso`); in degree `1` both sides are the common kernel functor `oneKer M`
(`Tor_iso_Tor'.oneIso`); and for `i = j + 2` the long exact sequences of the syzygy sequence
give `Tor_{j+2}(M, -) ≅ Tor_{j+1}(K, -)` and its `Tor'` analogue
(`Tor_iso_Tor'.torShift`, `Tor_iso_Tor'.tor'Shift`), the flanking terms vanishing because
`P₀ = Projective.over M` is projective, hence flat. Both shifts come from the *same* syzygy
sequence, which is what makes them compatible.

The long exact sequence of `leftDerived` for a short exact sequence of *objects*, obtained from
the homology long exact sequence of a degreewise short exact sequence of complexes, and the
horseshoe lemma are constructed in `TorShift` and `Horseshoe`.
-/

-- `Tor_iso_Tor'.fromLeftDerivedZero_natTrans`, `Tor_iso_Tor'.zeroIso`,
-- `lesShift.phi_preservesZeroMorphisms` and `lesShift.comp_naturality` rewrite through
-- `ModuleCat`/`Functor.leftDerived` bundling, which only unfolds with relaxed defeq transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

variable (R : Type u) [CommRing R]

/-- `tensorLeft M = M ⊗ -` preserves finite colimits. -/
@[ega "0 4.1.5" "special case", sga "4 IV 12.9" "special case", sga "5 V 1.2.1" "Module case"]
instance (priority := 100000) tensorLeft_preservesFiniteColimits (M : ModuleCat.{u} R) :
    Limits.PreservesFiniteColimits (MonoidalCategory.tensorLeft M) := by
  have adj : MonoidalCategory.tensorLeft M ⊣ (ihom M) := ihom.adjunction M
  have hpc : Limits.PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft M) :=
    adj.leftAdjoint_preservesColimits
  exact hpc.preservesFiniteColimits _

/-- `tensorRight N = - ⊗ N` preserves finite colimits. -/
@[ega "0 4.1.5" "special case",
  ega "III 7.2.5" "(c) ⇒ (a)",
  ega "III 7.2.6" "special case",
  sga "4 IV 12.9" "special case",
  sga "5 V 1.2.1" "Module case"]
instance (priority := 100000) tensorRight_preservesFiniteColimits (N : ModuleCat.{u} R) :
    Limits.PreservesFiniteColimits (MonoidalCategory.tensorRight N) := by
  have adj : MonoidalCategory.tensorRight N ⊣ (ihom N) :=
    (ihom.adjunction N).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight N)
  have hpc : Limits.PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorRight N) :=
    adj.leftAdjoint_preservesColimits
  exact hpc.preservesFiniteColimits _

/-- For a flat module `N`, `tensorRight N = - ⊗ N` preserves finite limits. -/
@[ega "III 6.1.1" "special case", sga "3 VIIB 3.3.3" "Clause"]
instance (priority := 100000) tensorRight_preservesFiniteLimits (N : ModuleCat.{u} R)
    [Module.Flat R N] :
    Limits.PreservesFiniteLimits (MonoidalCategory.tensorRight N) :=
  Limits.preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)

/-! ### Factoring the comparison through `Tor'`

Over the symmetric monoidal abelian category `C = ModuleCat R`:

* `Tor C i` sends `M ↦ leftDerived (tensorLeft M) i`, i.e. it derives the *second* variable
  of `M ⊗ -`; concretely `((Tor C i).obj M).obj N = ((tensorLeft M).leftDerived i).obj N`.
* `Tor' C i = (fun N ↦ leftDerived (tensorRight N) i).flip` derives the *first* variable;
  `((Tor' C i).obj M).obj N = ((tensorRight N).leftDerived i).obj M`.

The comparison of `Tor C i` with its own flip splits into two steps. The first,
`torFlip_iso_Tor' : (Tor C i).flip ≅ Tor' C i`, lifts the symmetric braiding
`tensorLeft M ≅ tensorRight M` through `NatTrans.leftDerived _ i`. The second,
`Tor_iso_Tor' : Tor C i ≅ Tor' C i`, is the balancing of `Tor`: deriving `M ⊗ -` in the second
variable agrees with deriving `- ⊗ N` in the first. Composing,
`Tor C i ≅ Tor' C i ≅ (Tor C i).flip`.
-/

open MonoidalCategory in
/-- For a fixed module `X`, the symmetric braiding `tensorLeft X ≅ tensorRight X` lifted
through `NatTrans.leftDerived · i` to an isomorphism of left-derived functors. -/
noncomputable def torFlip_iso_Tor'.derivedBraid (i : ℕ) (X : ModuleCat.{u} R) :
    (tensorLeft X).leftDerived i ≅ (tensorRight X).leftDerived i where
  hom := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight X).hom i
  inv := NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight X).inv i
  hom_inv_id := by rw [← NatTrans.leftDerived_comp]; simp [NatTrans.leftDerived_id]
  inv_hom_id := by rw [← NatTrans.leftDerived_comp]; simp [NatTrans.leftDerived_id]

open MonoidalCategory in
/-- The comparison `Tor C i ≅ (Tor' C i).flip`, pointwise the lifted braiding `derivedBraid`. -/
noncomputable def torFlip_iso_Tor'.inner (i : ℕ) :
    Tor (ModuleCat.{u} R) i ≅ (Tor' (ModuleCat.{u} R) i).flip :=
  NatIso.ofComponents (fun X => torFlip_iso_Tor'.derivedBraid R i X) (by
    intro X Y f
    change NatTrans.leftDerived ((tensoringLeft _).map f) i ≫ NatTrans.leftDerived _ i
       = NatTrans.leftDerived _ i ≫ NatTrans.leftDerived ((tensoringRight _).map f) i
    rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp]
    congr 1
    ext Z
    simp)

/-- The flip of `Tor` agrees with `Tor'`, via the symmetric braiding of `ModuleCat R` lifted
through `NatTrans.leftDerived`. -/
noncomputable def torFlip_iso_Tor' (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip ≅ Tor' (ModuleCat.{u} R) i :=
  (flipFunctor _ _ _).mapIso (torFlip_iso_Tor'.inner R i) ≪≫ eqToIso (Functor.flip_flip _)

/-! ### The balancing isomorphism by dimension shifting

The bifunctor isomorphism `Tor C i ≅ Tor' C i` (functors `C ⥤ C ⥤ C`) is assembled from a
per-first-variable isomorphism `(Tor C i).obj M ≅ (Tor' C i).obj M` of functors `C ⥤ C`
(`Tor_iso_Tor'.app`, natural in the second variable `N`) together with naturality in `M`
(`Tor_iso_Tor'.naturality`).

Fix `M`. The per-`M` isomorphism is built by induction on `i`, recursing on the first syzygy
`K := ker (Projective.π M)`:

* `Tor_iso_Tor'.zeroIso`: in degree `0` both `Tor` and `Tor'` are `M ⊗ -`, since `tensorLeft M`
  and `tensorRight N` are right exact (`Functor.leftDerivedZeroIsoSelf`), and the two
  identifications agree.
* `Tor_iso_Tor'.oneIso`: the case `i = 1`. From the long exact sequences of `Tor` and `Tor'`
  for the syzygy sequence `0 → K → P₀ → M → 0` with `P₀` projective, so that
  `Tor₁(P₀, -) = 0`, both sides are `ker (K ⊗ - ⟶ P₀ ⊗ -)`.
* `Tor_iso_Tor'.torShift` and `Tor_iso_Tor'.tor'Shift`: the dimension shift
  `Tor_{j+2}(M, -) ≅ Tor_{j+1}(K, -)`, from the same long exact sequence using
  `Torⱼ(P₀, -) = 0` for `j ≥ 1`, natural in `N`.

So `app 0 := zeroIso`, `app 1 := oneIso` and `app (j+2) := torShift ≪≫ app (j+1) K ≪≫
(tor'Shift).symm`. The two shifts are compatible because both connecting maps come from the
same syzygy sequence.

The long exact sequence of left-derived functors for a short exact sequence of *objects* comes
from the horseshoe short exact sequence of projective resolutions together with the homology
long exact sequence (`ShortComplex.ShortExact.homology_exact₁/₂/₃` and `.δ`).
-/

/-- The first syzygy of `M`: the kernel of the projective cover map `Projective.π M ↠ M`. -/
noncomputable def Tor_iso_Tor'.syzygy (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  Limits.kernel (Projective.π M)

/-- Naturality of `Functor.fromLeftDerivedZero` in the functor argument: for a natural
transformation `α : F ⟶ G` between additive functors, the degree-0 comparison maps
`fromLeftDerivedZero` commute with `α`. -/
theorem Tor_iso_Tor'.fromLeftDerivedZero_natTrans
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α := by
  ext X
  simp only [NatTrans.comp_app]
  rw [ProjectiveResolution.fromLeftDerivedZero_eq (projectiveResolution X) G,
      ProjectiveResolution.fromLeftDerivedZero_eq (projectiveResolution X) F]
  have step1 : (NatTrans.leftDerived α 0).app X ≫ ((projectiveResolution X).isoLeftDerivedObj G
      0).hom
      = ((projectiveResolution X).isoLeftDerivedObj F 0).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
            (projectiveResolution X).complex) := by
    simp only [NatTrans.leftDerived, Functor.whiskerRight_app,
      ProjectiveResolution.isoLeftDerivedObj, Iso.trans_hom, Functor.mapIso_hom]
    rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α (projectiveResolution X)]
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc]
    rw [← Functor.map_comp_assoc ((HomotopyCategory.homologyFunctor D (ComplexShape.down ℕ) 0))
        ((projectiveResolution X).isoLeftDerivedToHomotopyCategoryObj G).inv
        ((projectiveResolution X).isoLeftDerivedToHomotopyCategoryObj G).hom]
    rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    congr 1
    rw [Iso.app_hom, Iso.app_hom, ← Functor.comp_map]
    exact (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) 0).hom.naturality
      ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (projectiveResolution
          X).complex)
  have step2 : (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (projectiveResolution
            X).complex)
        ≫ ((ChainComplex.isoHomologyι₀ ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (projectiveResolution X).complex)).hom)
      = ((ChainComplex.isoHomologyι₀ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (projectiveResolution X).complex)).hom)
        ≫ HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
              (projectiveResolution X).complex) 0 := by
    rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq,
      HomologicalComplex.homologyFunctor_map]
    exact ChainComplex.isoHomologyι₀_inv_naturality
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (projectiveResolution
            X).complex)
  have step3 : HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (projectiveResolution
            X).complex) 0
        ≫ (projectiveResolution X).fromLeftDerivedZero' G
      = (projectiveResolution X).fromLeftDerivedZero' F ≫ α.app X := by
    apply (cancel_epi (HomologicalComplex.pOpcycles
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (projectiveResolution X).complex) 0)).mp
    rw [← Category.assoc, HomologicalComplex.p_opcyclesMap, Category.assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
      ← Category.assoc, ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
    simp [NatTrans.mapHomologicalComplex]
  rw [← Category.assoc, step1, Category.assoc]
  slice_lhs 2 3 => rw [step2]
  slice_lhs 3 4 => rw [step3]
  simp only [Category.assoc]

open MonoidalCategory in
/-- The degree-0 component `(Tor C 0).obj M ≅ (Tor' C 0).obj M`: both are naturally the tensor
functor `M ⊗ -`, via `Functor.leftDerivedZeroIsoSelf`. -/
noncomputable def Tor_iso_Tor'.zeroIso (M : ModuleCat.{u} R) :
    (Tor (ModuleCat.{u} R) 0).obj M ≅ (Tor' (ModuleCat.{u} R) 0).obj M :=
  NatIso.ofComponents
    (fun N => (Functor.leftDerivedZeroIsoSelf (tensorLeft M)).app N ≪≫
      ((Functor.leftDerivedZeroIsoSelf (tensorRight N)).app M).symm)
    (by
      intro N N' g
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
        Functor.leftDerivedZeroIsoSelf_hom]
      change ((tensorLeft M).leftDerived 0).map g ≫ (tensorLeft M).fromLeftDerivedZero.app N'
            ≫ (tensorRight N').leftDerivedZeroIsoSelf.inv.app M
          = ((tensorLeft M).fromLeftDerivedZero.app N ≫ (tensorRight
              N).leftDerivedZeroIsoSelf.inv.app M)
            ≫ (NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map g) 0).app M
      have hnatL := (tensorLeft M).fromLeftDerivedZero.naturality g
      rw [← Category.assoc, hnatL, Category.assoc, Category.assoc]
      congr 1
      have hhelp := Tor_iso_Tor'.fromLeftDerivedZero_natTrans
        ((tensoringRight (ModuleCat.{u} R)).map g)
      have hinv : (tensorRight N).leftDerivedZeroIsoSelf.inv
          ≫ NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map g) 0
          = (tensoringRight (ModuleCat.{u} R)).map g
              ≫ (tensorRight N').leftDerivedZeroIsoSelf.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        simp only [Functor.leftDerivedZeroIsoSelf_hom]
        exact hhelp
      have h2 := NatTrans.congr_app hinv M
      simp only [NatTrans.comp_app] at h2
      exact h2.symm)

/-! ### The `Tor` long exact sequence in the first variable

The long exact sequence of `Tor(-, N)` for a short exact sequence `0 → A → B → C → 0` of objects
in the first (non-derived) variable, natural in `N`, together with the vanishing of
`Tor_{n+1}(P, -)` for flat `P`:

* `Q_• = (projectiveResolution N).complex` is a projective, hence flat, resolution of `N`.
* Tensoring the sequence with each `Q_q` is exact by flatness, giving a degreewise short exact
  sequence of complexes `0 → A⊗Q_• → B⊗Q_• → C⊗Q_• → 0`.
* Its homology long exact sequence (`ShortComplex.ShortExact.δ`, `.homology_exact₁/₂/₃`, and
  `δIso` when the middle complex `B⊗Q_•` has vanishing homology) transports to `Tor` along
  `ProjectiveResolution.isoLeftDerivedObj`.
* The middle vanishes because `B` flat makes `B ⊗ Q_•` acyclic in positive degrees; this is
  `Tor_iso_Tor'.tor_flat_isZero`.
-/

/-- The short complex `0 → syzygy M → Projective.over M → M → 0`, with
`f = kernel.ι (Projective.π M)` and `g = Projective.π M`. -/
noncomputable def Tor_iso_Tor'.syzygySC (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (Limits.kernel.ι (Projective.π M)) (Projective.π M)
    (by simp)

/-- The syzygy short complex is short exact. -/
theorem Tor_iso_Tor'.syzygySC_shortExact (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.syzygySC R M).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := by dsimp [Tor_iso_Tor'.syzygySC]; infer_instance
  epi_g := by dsimp [Tor_iso_Tor'.syzygySC]; infer_instance

open MonoidalCategory in
/-- For a flat object `P`, the higher `Tor` in the *first* variable vanishes:
`Tor_{n+1}(P, N) = 0`. -/
@[ega "0 6.1.1" "(a) ⇒ (b)",
  ega "III 6.5.8" "Affine case",
  sga "1 IV 5.2" "B = A: (ii) ⇒ (i)",
  sga "1 IV 5.5" "(i)⇒(ii)",
  sga "4 XVII 4.1.9" "special case",
  sga "6 III 1.5" "special case",
  sga "7 VIII 1.2" "special case"]
theorem Tor_iso_Tor'.tor_flat_isZero (P N : ModuleCat.{u} R) [Module.Flat R P] (n : ℕ) :
    Limits.IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj P).obj N) := by
  have hiso := (projectiveResolution N).isoLeftDerivedObj (tensorLeft P) (n + 1)
  refine Limits.IsZero.of_iso ?_ hiso
  have hexact : ((projectiveResolution N).complex.sc (n + 1)).Exact :=
    (HomologicalComplex.exactAt_iff _ _).mp
      ((projectiveResolution N).complex_exactAt_succ n)
  have hmap : (((tensorLeft P).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution N).complex).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff]
    exact hexact.map_of_preservesLeftHomologyOf (tensorLeft P)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hmap

/-! ### Dimension shift from a short exact sequence with flat middle term

For a short exact sequence `S : 0 → A → B → C → 0` of objects whose middle term `B` is flat,
the connecting maps of the `Tor` long exact sequence give an isomorphism
`(Tor (n+2)).obj C ≅ (Tor (n+1)).obj A` of functors `C ⥤ C` in the second variable `N`: both
flanking terms `Tor_{n+2}(B, -)` and `Tor_{n+1}(B, -)` vanish by `tor_flat_isZero`.

The shift `(n+1) ↦ n` is false at `n = 0`: there the bottom of the long exact sequence is
`0 → Tor₁(C, N) → A⊗N → B⊗N`, so `Tor₁(C, N) ≅ ker (A⊗N → B⊗N)`, a proper submodule of
`A⊗N = (Tor 0).obj A` in general — take `R = ℤ` and `0 → ℤ →⁽ˣ²⁾ ℤ → ℤ/2 → 0` with `N = ℤ`, where
the left side is `0` and the right side is `ℤ`.
-/
section lesShiftAux
open CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex
open HomologicalComplex.HomologySequence

/-- The bifunctor `X ↦ (tensorLeft X).mapHomologicalComplex`. -/
noncomputable def lesShift.phiBi :
    ModuleCat.{u} R ⥤ HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ) ⥤
      HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ) where
  obj X := (tensorLeft X).mapHomologicalComplex (ComplexShape.down ℕ)
  map {X Y} f := NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat.{u} R)).map f) (ComplexShape.down ℕ)
  map_id := by intro X; simp
  map_comp := by intro X Y Z f g; simp

/-- The functor `X ↦ X ⊗ Q_•` for a fixed complex `Q`. -/
noncomputable def lesShift.phi
    (Q : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :
    ModuleCat.{u} R ⥤ HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ) :=
  (lesShift.phiBi R).flip.obj Q

/-- `lesShift.phi R Q` preserves zero morphisms. -/
instance (priority := 100000) lesShift.phi_preservesZeroMorphisms
    (Q : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :
    (lesShift.phi R Q).PreservesZeroMorphisms where
  map_zero X Y := by dsimp [lesShift.phi, lesShift.phiBi]; ext i; simp

/-- Tensoring the short exact sequence `S` (in the first variable) with the projective resolution
of `N` gives a short exact sequence of complexes. -/
theorem lesShift.ses (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) :
    (S.map (lesShift.phi R (projectiveResolution N).complex)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  show (S.map (tensorRight ((projectiveResolution N).complex.X q))).ShortExact
  have hflat : Module.Flat R ((projectiveResolution N).complex.X q) := by infer_instance
  exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hS
    (tensorRight ((projectiveResolution N).complex.X q)) _
    (tensorRight_preservesFiniteLimits R ((projectiveResolution N).complex.X q))
    (tensorRight_preservesFiniteColimits R ((projectiveResolution N).complex.X q))

/-- Naturality of `S.mapNatTrans` composed with `mapShortComplex`: a commuting square. -/
theorem lesShift.mapShortComplex_mapNatTrans_comm {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G)
    {S₁ S₂ : ShortComplex C} (ψ : S₁ ⟶ S₂) :
    F.mapShortComplex.map ψ ≫ S₂.mapNatTrans α = S₁.mapNatTrans α ≫ G.mapShortComplex.map ψ := by
  ext <;> exact (α.naturality _)

/-- A morphism of short exact sequences of complexes induces a morphism of the associated
snake inputs. -/
noncomputable def lesShift.snakeHom {ι : Type} {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (ψ : S₁ ⟶ S₂) (i j : ι) (hij : c.Rel i j) :
    (snakeInput hS₁ i j hij) ⟶ (snakeInput hS₂ i j hij) where
  f₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c i).mapShortComplex.map ψ
  f₁ := (HomologicalComplex.opcyclesFunctor (ModuleCat.{u} R) c i).mapShortComplex.map ψ
  f₂ := (HomologicalComplex.cyclesFunctor (ModuleCat.{u} R) c j).mapShortComplex.map ψ
  f₃ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c j).mapShortComplex.map ψ
  comm₀₁ := by simp only [snakeInput_v₀₁]; exact lesShift.mapShortComplex_mapNatTrans_comm _ ψ
  comm₁₂ := by simp only [snakeInput_v₁₂]; exact lesShift.mapShortComplex_mapNatTrans_comm _ ψ
  comm₂₃ := by simp only [snakeInput_v₂₃]; exact lesShift.mapShortComplex_mapNatTrans_comm _ ψ

/-- Naturality of the connecting homomorphism `δ` for a morphism of short exact sequences of
complexes. -/
theorem lesShift.δ_naturality {ι : Type} {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (ψ : S₁ ⟶ S₂) (i j : ι) (hij : c.Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap ψ.τ₁ j
      = HomologicalComplex.homologyMap ψ.τ₃ i ≫ hS₂.δ i j hij :=
  SnakeInput.naturality_δ (lesShift.snakeHom R hS₁ hS₂ ψ i j hij)

/-- Conjugating a commuting square of isomorphisms: from `a ≫ p.hom = q.hom ≫ b` one gets
`b ≫ p.inv = q.inv ≫ a`. -/
theorem lesShift.comp_inv_eq_inv_comp_of_comm {C : Type*} [Category C] {A A' B B' : C}
    (a : A ⟶ A') (p : A' ≅ B') (q : A ≅ B) (b : B ⟶ B')
    (hC : a ≫ p.hom = q.hom ≫ b) :
    b ≫ p.inv = q.inv ≫ a := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hC]

/-- The per-`N` component of `lesShift`: the connecting isomorphism of the tensored short exact
sequence of complexes, transported to `Tor` along `isoLeftDerivedObj`. -/
@[ega "III 7.6.11" "more general"]
noncomputable def lesShift.comp (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Flat R S.X₂] (n : ℕ) (N : ModuleCat.{u} R) :
    (((Tor (ModuleCat.{u} R) (n + 2)).obj S.X₃).obj N)
      ≅ (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁).obj N) :=
  ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₃) (n+2)) ≪≫
    (lesShift.ses R S hS N).δIso (n+2) (n+1) (by simp [ComplexShape.down_Rel])
      (Limits.IsZero.of_iso (Tor_iso_Tor'.tor_flat_isZero R S.X₂ N (n+1))
            ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₂) (n+2)).symm)
      (Limits.IsZero.of_iso (Tor_iso_Tor'.tor_flat_isZero R S.X₂ N n)
            ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₂) (n+1)).symm) ≪≫
    ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₁) (n + 1)).symm

/-- Naturality of `lesShift.comp` with respect to any morphism `ψ` of the tensored short exact
sequences of complexes, once the outer `isoLeftDerivedObj` squares commute. -/
private theorem lesShift.comp_naturality_of_comm {S S' : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) [Module.Flat R S.X₂] [Module.Flat R S'.X₂]
    (n : ℕ) {N N' : ModuleCat.{u} R}
    (ψ : S.map (lesShift.phi R (projectiveResolution N).complex) ⟶
      S'.map (lesShift.phi R (projectiveResolution N').complex))
    (F₃ : ((Tor (ModuleCat.{u} R) (n + 2)).obj S.X₃).obj N ⟶
      ((Tor (ModuleCat.{u} R) (n + 2)).obj S'.X₃).obj N')
    (F₁ : ((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁).obj N ⟶
      ((Tor (ModuleCat.{u} R) (n + 1)).obj S'.X₁).obj N')
    (hA : F₃ ≫ ((projectiveResolution N').isoLeftDerivedObj (tensorLeft S'.X₃) (n + 2)).hom
      = ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₃) (n + 2)).hom ≫
        HomologicalComplex.homologyMap ψ.τ₃ (n + 2))
    (hC : F₁ ≫ ((projectiveResolution N').isoLeftDerivedObj (tensorLeft S'.X₁) (n + 1)).hom
      = ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₁) (n + 1)).hom ≫
        HomologicalComplex.homologyMap ψ.τ₁ (n + 1)) :
    F₃ ≫ (lesShift.comp R S' hS' n N').hom = (lesShift.comp R S hS n N).hom ≫ F₁ := by
  have hB := lesShift.δ_naturality R (lesShift.ses R S hS N) (lesShift.ses R S' hS' N') ψ (n + 2)
    (n + 1) (by simp [ComplexShape.down_Rel])
  have hC' := lesShift.comp_inv_eq_inv_comp_of_comm _ _ _ _ hC
  simp only [lesShift.comp, Iso.trans_hom, Iso.symm_hom, ShortComplex.ShortExact.δIso, asIso_hom,
    Category.assoc]
  rw [← Category.assoc, hA, Category.assoc,
      ← Category.assoc (HomologicalComplex.homologyMap ψ.τ₃ (n+2)), ← hB, Category.assoc, hC']

/-- Naturality in `N` of the component iso `lesShift.comp`. -/
theorem lesShift.comp_naturality (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Flat R S.X₂] (n : ℕ) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor (ModuleCat.{u} R) (n+2)).obj S.X₃).map g ≫ (lesShift.comp R S hS n N').hom
      = (lesShift.comp R S hS n N).hom ≫ ((Tor (ModuleCat.{u} R) (n+1)).obj S.X₁).map g := by
  let φ := ProjectiveResolution.lift g (projectiveResolution N) (projectiveResolution N')
  have hφ : φ.f 0 ≫ (projectiveResolution N').π.f 0 = (projectiveResolution N).π.f 0 ≫ g :=
    ProjectiveResolution.lift_commutes_zero g _ _
  exact lesShift.comp_naturality_of_comm R hS hS n (S.mapNatTrans ((lesShift.phiBi R).flip.map φ))
    _ _
    (ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
      (projectiveResolution N) (projectiveResolution N') φ hφ (tensorLeft S.X₃) (n+2))
    (ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
      (projectiveResolution N) (projectiveResolution N') φ hφ (tensorLeft S.X₁) (n+1))

/-- Naturality of `isoLeftDerivedObj` in the first variable `f : X ⟶ Y`, at a fixed `N`. -/
private theorem lesShift.isoLeftDerivedObj_hom_naturality_left {X Y : ModuleCat.{u} R}
    (f : X ⟶ Y) (k : ℕ) (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) k).map f).app N ≫
        ((projectiveResolution N).isoLeftDerivedObj (tensorLeft Y) k).hom
      = ((projectiveResolution N).isoLeftDerivedObj (tensorLeft X) k).hom ≫
        HomologicalComplex.homologyMap
          ((lesShift.phi R (projectiveResolution N).complex).map f) k := by
  have h := ProjectiveResolution.leftDerived_app_eq
    ((tensoringLeft (ModuleCat.{u} R)).map f) (projectiveResolution N) k
  rw [show ((Tor (ModuleCat.{u} R) k).map f).app N
        = (NatTrans.leftDerived ((tensoringLeft (ModuleCat.{u} R)).map f) k).app N from rfl,
    h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Naturality of the component iso `lesShift.comp` at a fixed `N` in the short exact sequence,
for a morphism `Φ : S ⟶ S'` of short exact sequences. -/
theorem lesShift.comp_naturality_S {S S' : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) [Module.Flat R S.X₂] [Module.Flat R S'.X₂]
    (n : ℕ) (Φ : S ⟶ S') (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) (n+2)).map Φ.τ₃).app N ≫ (lesShift.comp R S' hS' n N).hom
      = (lesShift.comp R S hS n N).hom ≫ ((Tor (ModuleCat.{u} R) (n+1)).map Φ.τ₁).app N :=
  lesShift.comp_naturality_of_comm R hS hS' n
    ((lesShift.phi R (projectiveResolution N).complex).mapShortComplex.map Φ) _ _
    (lesShift.isoLeftDerivedObj_hom_naturality_left R Φ.τ₃ (n+2) N)
    (lesShift.isoLeftDerivedObj_hom_naturality_left R Φ.τ₁ (n+1) N)

/-- The dimension shift `(Tor (n+2)).obj S.X₃ ≅ (Tor (n+1)).obj S.X₁` for a short exact
sequence `S` with flat middle term, as an isomorphism of functors in the second variable. -/
@[ega "III 7.6.11" "more general"]
noncomputable def Tor_iso_Tor'.lesShift00M3 (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) [Module.Flat R S.X₂] (n : ℕ) :
    (Tor (ModuleCat.{u} R) (n + 2)).obj S.X₃
      ≅ (Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁ :=
  NatIso.ofComponents (fun N => lesShift.comp R S hS n N)
    (fun g => lesShift.comp_naturality R S hS n g)

end lesShiftAux

/-- `Projective.over M`, the middle term of the syzygy sequence, is flat. -/
theorem Tor_iso_Tor'.torShift_flat_mid (M : ModuleCat.{u} R) :
    Module.Flat R (Tor_iso_Tor'.syzygySC R M).X₂ := by
  have : (Tor_iso_Tor'.syzygySC R M).X₂ = Projective.over M := rfl
  rw [this]
  infer_instance

/-- The dimension shift `(Tor C (j+2)).obj M ≅ (Tor C (j+1)).obj K` for `Tor`, natural in `N`,
where `K = Tor_iso_Tor'.syzygy M`. -/
noncomputable def Tor_iso_Tor'.torShift (j : ℕ) (M : ModuleCat.{u} R) :
    (Tor (ModuleCat.{u} R) (j + 2)).obj M
      ≅ (Tor (ModuleCat.{u} R) (j + 1)).obj (Tor_iso_Tor'.syzygy R M) :=
  haveI : Module.Flat R (Tor_iso_Tor'.syzygySC R M).X₂ := Tor_iso_Tor'.torShift_flat_mid R M
  Tor_iso_Tor'.lesShift00M3 R (Tor_iso_Tor'.syzygySC R M)
    (Tor_iso_Tor'.syzygySC_shortExact R M) j

/- `Tor_iso_Tor'.tor'Shift` (dimension shift for `Tor'`, `j ≥ 1`) is defined further below,
after the `horseshoe`/`tor'LES_ses` infrastructure (it reuses the same engine as
`oneIso_tor'Ker`); see just before `Tor_iso_Tor'.app`. -/

/-! ### Degree one, via a common kernel description

Both `(Tor C 1).obj M` and `(Tor' C 1).obj M`, as functors `C ⥤ C` in `N`, are identified with
the *same* functor `oneKer M`: the kernel of the natural transformation `K ⊗ - ⟶ P₀ ⊗ -` induced
by the syzygy inclusion `kernel.ι (Projective.π M) : K ⟶ P₀`, where `K = syzygy M` and
`P₀ = Projective.over M`. Concretely `oneKer M` is the kernel, in the abelian functor category
`C ⥤ C`, of `(tensoringLeft C).map (kernel.ι (Projective.π M))`.

* `oneIso_torKer : (Tor C 1).obj M ≅ oneKer M` comes from the bottom of the first-variable
  `Tor` long exact sequence for the syzygy sequence, i.e. from the `lesShift.ses`-tensored
  sequence of complexes: the connecting map `δ` at `(1, 0)` is a monomorphism whose image is
  the kernel of `Tor₀(K) → Tor₀(P₀)`, because `Tor₁(P₀, N) = 0` by `tor_flat_isZero`, and `Tor₀`
  is identified with `⊗` by `Functor.leftDerivedZeroIsoSelf`.
* `oneIso_tor'Ker : (Tor' C 1).obj M ≅ oneKer M` is the same readout on the `Tor'` side, where
  the first variable is derived. It needs the horseshoe long exact sequence for the syzygy
  sequence, with `Tor'₁(P₀, N) = 0` by `isZero_Tor'_succ_of_projective`.
* `oneIso M := oneIso_torKer ≪≫ (oneIso_tor'Ker).symm`.

Both identifications are natural in `N`.
-/

open MonoidalCategory in
/-- The kernel functor `N ↦ ker(K ⊗ N → P₀ ⊗ N)`, where `K = syzygy M ↪ P₀ = Projective.over M`
via `kernel.ι (Projective.π M)`: the kernel, in the abelian functor category `C ⥤ C`, of
`(tensoringLeft C).map (kernel.ι _) : tensorLeft K ⟶ tensorLeft P₀`. -/
noncomputable def Tor_iso_Tor'.oneKer (M : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  Limits.kernel ((tensoringLeft (ModuleCat.{u} R)).map
    (Limits.kernel.ι (Projective.π M)))

section oneIsoTorKerAux
open CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex
open HomologicalComplex.HomologySequence

/-- The tensored syzygy short complex of complexes, as a function of `N`:
`0 → K⊗Q_•(N) → P₀⊗Q_•(N) → M⊗Q_•(N) → 0`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_S (M N : ModuleCat.{u} R) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  (Tor_iso_Tor'.syzygySC R M).map
    (lesShift.phi R (projectiveResolution N).complex)

/-- `S(N)` is short exact (degreewise short exact since each `Q_q` is flat). -/
theorem Tor_iso_Tor'.oneIsoTK_S_shortExact (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_S R M N).ShortExact :=
  lesShift.ses R _ (Tor_iso_Tor'.syzygySC_shortExact R M) N

/-- `e1`: `Tor_1(M,N) ≅ H_1(S(N).X₃)`, where `S(N).X₃ = M ⊗ Q_•(N)`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_e1 (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj N ≅ (Tor_iso_Tor'.oneIsoTK_S R M N).X₃.homology 1 :=
  (projectiveResolution N).isoLeftDerivedObj (tensorLeft M) 1

/-- The middle complex of `S(N)` has vanishing degree-1 homology (since `P₀` is flat). -/
theorem Tor_iso_Tor'.oneIsoTK_hP (M N : ModuleCat.{u} R) :
    Limits.IsZero ((Tor_iso_Tor'.oneIsoTK_S R M N).X₂.homology 1) := by
  have : Module.Flat R ((Tor_iso_Tor'.syzygySC R M).X₂) :=
    Tor_iso_Tor'.torShift_flat_mid R M
  have hz := Tor_iso_Tor'.tor_flat_isZero R ((Tor_iso_Tor'.syzygySC R M).X₂) N 0
  exact Limits.IsZero.of_iso hz
    ((projectiveResolution N).isoLeftDerivedObj
      (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)) 1).symm

/-- `e3`: `H_1(S(N).X₃) ≅ kernel (homologyMap S(N).f 0)`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_e3 (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_S R M N).X₃.homology 1 ≅
      Limits.kernel (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0) :=
  haveI hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  haveI hmono : Mono ((Tor_iso_Tor'.oneIsoTK_S_shortExact R M N).δ 1 0 hrel) :=
    (Tor_iso_Tor'.oneIsoTK_S_shortExact R M N).mono_δ 1 0 hrel (Tor_iso_Tor'.oneIsoTK_hP R M N)
  IsLimit.conePointUniqueUpToIso
    ((Tor_iso_Tor'.oneIsoTK_S_shortExact R M N).homology_exact₁ 1 0 hrel).fIsKernel
    (Limits.limit.isLimit _)

/-- The degree-0 comparison `p : H_0(S(N).X₁) ≅ K ⊗ N`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_p (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_S R M N).X₁.homology 0 ≅
      (tensorLeft (Tor_iso_Tor'.syzygy R M)).obj N :=
  ((projectiveResolution N).isoLeftDerivedObj
      (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).symm ≪≫
    (Functor.leftDerivedZeroIsoSelf (tensorLeft (Tor_iso_Tor'.syzygy R M))).app N

/-- The degree-0 comparison `q : H_0(S(N).X₂) ≅ P₀ ⊗ N`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_q (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_S R M N).X₂.homology 0 ≅
      (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)).obj N :=
  ((projectiveResolution N).isoLeftDerivedObj
      (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)) 0).symm ≪≫
    (Functor.leftDerivedZeroIsoSelf
      (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂))).app N

/-- The `oneKer` defining map at `N` (Tor side): `K ⊗ N → P₀ ⊗ N`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_κ (M N : ModuleCat.{u} R) :
    (tensorLeft (Tor_iso_Tor'.syzygy R M)).obj N ⟶
      (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)).obj N :=
  ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M))).app N

/-- The comm square identifying `homologyMap S(N).f 0` with `κ`. -/
theorem Tor_iso_Tor'.oneIsoTK_hsq (M N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0
        ≫ (Tor_iso_Tor'.oneIsoTK_q R M N).hom
      = (Tor_iso_Tor'.oneIsoTK_p R M N).hom ≫ Tor_iso_Tor'.oneIsoTK_κ R M N := by
  show HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0 ≫
      ((projectiveResolution N).isoLeftDerivedObj
          (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)) 0).inv ≫
        (Functor.leftDerivedZeroIsoSelf
          (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂))).hom.app N
    = (((projectiveResolution N).isoLeftDerivedObj
          (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).inv ≫
        (Functor.leftDerivedZeroIsoSelf
          (tensorLeft (Tor_iso_Tor'.syzygy R M))).hom.app N) ≫
        Tor_iso_Tor'.oneIsoTK_κ R M N
  have hlde := ProjectiveResolution.leftDerived_app_eq
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))
    (projectiveResolution N) 0
  have hSf : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0
      = (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          ((NatTrans.mapHomologicalComplex
            ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))
            (ComplexShape.down ℕ)).app (projectiveResolution N).complex) := rfl
  have hnat' : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0
        ≫ ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft ((Tor_iso_Tor'.syzygySC R M).X₂)) 0).inv
      = ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).inv
        ≫ (NatTrans.leftDerived
            ((tensoringLeft (ModuleCat.{u} R)).map
              (Limits.kernel.ι (Projective.π M))) 0).app N := by
    show (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          ((NatTrans.mapHomologicalComplex
            ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))
            (ComplexShape.down ℕ)).app (projectiveResolution N).complex)
        ≫ ((projectiveResolution N).isoLeftDerivedObj
            ((tensoringLeft (ModuleCat.{u} R)).obj (Projective.over M)) 0).inv
      = ((projectiveResolution N).isoLeftDerivedObj
            ((tensoringLeft (ModuleCat.{u} R)).obj (Limits.kernel (Projective.π M))) 0).inv
        ≫ (NatTrans.leftDerived
            ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M))) 0).app N
    rw [hlde, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hnat', Category.assoc, Category.assoc]
  congr 1
  have hfd := Tor_iso_Tor'.fromLeftDerivedZero_natTrans
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))
  have hfd' := congrArg (fun t => NatTrans.app t N) hfd
  simp only [NatTrans.comp_app] at hfd'
  simp only [Functor.leftDerivedZeroIsoSelf_hom]
  exact hfd'

/-- `e4`: `kernel (homologyMap S(N).f 0) ≅ kernel κ`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_e4 (M N : ModuleCat.{u} R) :
    Limits.kernel (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0) ≅
      Limits.kernel (Tor_iso_Tor'.oneIsoTK_κ R M N) :=
  Limits.kernel.mapIso (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0)
    (Tor_iso_Tor'.oneIsoTK_κ R M N) (Tor_iso_Tor'.oneIsoTK_p R M N) (Tor_iso_Tor'.oneIsoTK_q R M N)
    (Tor_iso_Tor'.oneIsoTK_hsq R M N)

/-- `e5`: `kernel κ ≅ (oneKer M).obj N`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_e5 (M N : ModuleCat.{u} R) :
    Limits.kernel (Tor_iso_Tor'.oneIsoTK_κ R M N) ≅ (Tor_iso_Tor'.oneKer R M).obj N :=
  (PreservesKernel.iso ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj N)
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))).symm

/-- The per-`N` component of `oneIso_torKer`, assembled from the four steps. -/
@[ega "IV 11.2.3" "Tor₁ᴬ(M, special case"]
noncomputable def Tor_iso_Tor'.oneIsoTK_comp (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj N ≅ (Tor_iso_Tor'.oneKer R M).obj N :=
  Tor_iso_Tor'.oneIsoTK_e1 R M N ≪≫ Tor_iso_Tor'.oneIsoTK_e3 R M N ≪≫
    Tor_iso_Tor'.oneIsoTK_e4 R M N ≪≫ Tor_iso_Tor'.oneIsoTK_e5 R M N

/-- The lift of `g : N ⟶ N'` to projective resolutions. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_lift
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (projectiveResolution N).complex ⟶ (projectiveResolution N').complex :=
  ProjectiveResolution.lift g (projectiveResolution N) (projectiveResolution N')

/-- The lift `oneIsoTK_lift g` is compatible in degree `0` with the augmentations:
`lift.f 0 ≫ π' = π ≫ g`. -/
theorem Tor_iso_Tor'.oneIsoTK_lift_comm
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (Tor_iso_Tor'.oneIsoTK_lift R g).f 0 ≫ (projectiveResolution N').π.f 0
      = (projectiveResolution N).π.f 0 ≫ g :=
  ProjectiveResolution.lift_commutes_zero g _ _

/-- The morphism of short complexes of complexes `S(N) ⟶ S(N')` induced by `g`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_φ (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    Tor_iso_Tor'.oneIsoTK_S R M N ⟶ Tor_iso_Tor'.oneIsoTK_S R M N' :=
  (Tor_iso_Tor'.syzygySC R M).mapNatTrans
    ((lesShift.phiBi R).flip.map (Tor_iso_Tor'.oneIsoTK_lift R g))

/-- Naturality in `N` of the comparison `e1 : Tor_1(M, N) ≅ H_1(M ⊗ Q_•(N))`. -/
theorem Tor_iso_Tor'.oneIsoTK_e1_naturality (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor (ModuleCat.{u} R) 1).obj M).map g ≫ (Tor_iso_Tor'.oneIsoTK_e1 R M N').hom
      = (Tor_iso_Tor'.oneIsoTK_e1 R M N).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₃ 1 :=
  ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
    (projectiveResolution N) (projectiveResolution N')
    (Tor_iso_Tor'.oneIsoTK_lift R g) (Tor_iso_Tor'.oneIsoTK_lift_comm R g)
    (tensorLeft M) 1

/-- `e3` characterization: `e3.hom ≫ kernel.ι = δ`. -/
theorem Tor_iso_Tor'.oneIsoTK_e3_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_e3 R M N).hom ≫
        Limits.kernel.ι (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0)
      = (Tor_iso_Tor'.oneIsoTK_S_shortExact R M N).δ 1 0 (by simp [ComplexShape.down_Rel]) := by
  dsimp only [Tor_iso_Tor'.oneIsoTK_e3]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ (Limits.limit.isLimit _) WalkingParallelPair.zero

/-- Commutativity of the degree-0 homology square induced by `g`. -/
theorem Tor_iso_Tor'.oneIsoTK_kerComm (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0 ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₂ 0
      = HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₁ 0 ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N').f 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  exact (Tor_iso_Tor'.oneIsoTK_φ R M g).comm₁₂.symm

/-- `e3` naturality square. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIsoTK_e3_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₃ 1 ≫
        (Tor_iso_Tor'.oneIsoTK_e3 R M N').hom
      = (Tor_iso_Tor'.oneIsoTK_e3 R M N).hom ≫
        Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₂ 0)
          (Tor_iso_Tor'.oneIsoTK_kerComm R M g) := by
  apply (cancel_mono (Limits.kernel.ι
    (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N').f 0))).mp
  rw [Category.assoc, Category.assoc, Tor_iso_Tor'.oneIsoTK_e3_hom_ι,
    Limits.kernel.lift_ι, ← Category.assoc, Tor_iso_Tor'.oneIsoTK_e3_hom_ι]
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  exact (HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.oneIsoTK_φ R M g)
    (Tor_iso_Tor'.oneIsoTK_S_shortExact R M N) (Tor_iso_Tor'.oneIsoTK_S_shortExact R M N')
    1 0 hrel).symm

/-- The natural transformation defining `oneKer M`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_η (M : ModuleCat.{u} R) :
    (tensoringLeft (ModuleCat.{u} R)).obj (Tor_iso_Tor'.syzygy R M) ⟶
      (tensoringLeft (ModuleCat.{u} R)).obj ((Tor_iso_Tor'.syzygySC R M).X₂) :=
  (tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M))

/-- `e5` compatibility with `kernel.ι`. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIsoTK_e5_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_e5 R M N).hom ≫ (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N
      = Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_κ R M N) := by
  dsimp only [Tor_iso_Tor'.oneIsoTK_e5]
  exact PreservesKernel.iso_inv_ι ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj N)
    (Tor_iso_Tor'.oneIsoTK_η R M)

/-- Naturality of the degree-0 comparison `p`. -/
theorem Tor_iso_Tor'.oneIsoTK_p_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₁ 0 ≫
        (Tor_iso_Tor'.oneIsoTK_p R M N').hom
      = (Tor_iso_Tor'.oneIsoTK_p R M N).hom ≫
        ((tensoringLeft (ModuleCat.{u} R)).obj (Tor_iso_Tor'.syzygy R M)).map g := by
  have hτ₁ : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₁ 0
      = ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).inv ≫
          ((tensorLeft (Tor_iso_Tor'.syzygy R M)).leftDerived 0).map g ≫
          ((projectiveResolution N').isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).hom := by
    have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
      (projectiveResolution N) (projectiveResolution N')
      (Tor_iso_Tor'.oneIsoTK_lift R g) (Tor_iso_Tor'.oneIsoTK_lift_comm R g)
      (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0
    show ((tensorLeft (Tor_iso_Tor'.syzygy R M)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          (Tor_iso_Tor'.oneIsoTK_lift R g)
        = ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).inv ≫
          ((tensorLeft (Tor_iso_Tor'.syzygy R M)).leftDerived 0).map g ≫
          ((projectiveResolution N').isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).hom
    rw [h, Iso.inv_hom_id_assoc]
  dsimp only [Tor_iso_Tor'.oneIsoTK_p]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.leftDerivedZeroIsoSelf_hom,
    Category.assoc]
  rw [hτ₁]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  have hnatL := (tensorLeft (Tor_iso_Tor'.syzygy R M)).fromLeftDerivedZero.naturality g
  rw [hnatL]

/-- `e4` compatibility with `kernel.ι`. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIsoTK_e4_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIsoTK_e4 R M N).hom ≫ Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_κ R M N)
      = Limits.kernel.ι (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M N).f 0) ≫
        (Tor_iso_Tor'.oneIsoTK_p R M N).hom := by
  dsimp only [Tor_iso_Tor'.oneIsoTK_e4, Limits.kernel.mapIso]
  exact Limits.kernel.lift_ι _ _ _

/-- The combined `e4 ≫ e5` naturality square. -/
theorem Tor_iso_Tor'.oneIsoTK_e45_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_φ R M g).τ₂ 0)
          (Tor_iso_Tor'.oneIsoTK_kerComm R M g) ≫
        ((Tor_iso_Tor'.oneIsoTK_e4 R M N').hom ≫ (Tor_iso_Tor'.oneIsoTK_e5 R M N').hom)
      = ((Tor_iso_Tor'.oneIsoTK_e4 R M N).hom ≫ (Tor_iso_Tor'.oneIsoTK_e5 R M N).hom) ≫
        (Tor_iso_Tor'.oneKer R M).map g := by
  apply (cancel_mono ((Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N')).mp
  have hιnat : (Tor_iso_Tor'.oneKer R M).map g ≫ (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R
      M)).app N'
      = (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N ≫
        ((tensoringLeft (ModuleCat.{u} R)).obj (Tor_iso_Tor'.syzygy R M)).map g :=
    (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).naturality g
  simp only [Category.assoc]
  rw [hιnat]
  simp only [Tor_iso_Tor'.oneIsoTK_e5_hom_ι_assoc, Tor_iso_Tor'.oneIsoTK_e5_hom_ι,
    Tor_iso_Tor'.oneIsoTK_e4_hom_ι_assoc, Tor_iso_Tor'.oneIsoTK_e4_hom_ι]
  rw [← Category.assoc, Limits.kernel.lift_ι]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIsoTK_p_naturality R M g]

/-- Naturality in `N` of the composite comparison `Tor_1(M, N) ≅ (oneKer M).obj N`. -/
theorem Tor_iso_Tor'.oneIsoTK_comp_naturality (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor (ModuleCat.{u} R) 1).obj M).map g ≫ (Tor_iso_Tor'.oneIsoTK_comp R M N').hom
      = (Tor_iso_Tor'.oneIsoTK_comp R M N).hom ≫ (Tor_iso_Tor'.oneKer R M).map g := by
  simp only [Tor_iso_Tor'.oneIsoTK_comp, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (((Tor (ModuleCat.{u} R) 1).obj M).map g),
    Tor_iso_Tor'.oneIsoTK_e1_naturality]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIsoTK_e3_naturality_assoc, Tor_iso_Tor'.oneIsoTK_e45_naturality]
  simp only [Category.assoc]

/-- Tor-side kernel description: `(Tor C 1).obj M ≅ oneKer M`, natural in `N`. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def Tor_iso_Tor'.oneIso_torKer (M : ModuleCat.{u} R) :
    (Tor (ModuleCat.{u} R) 1).obj M ≅ Tor_iso_Tor'.oneKer R M :=
  NatIso.ofComponents (fun N => Tor_iso_Tor'.oneIsoTK_comp R M N)
    (fun g => Tor_iso_Tor'.oneIsoTK_comp_naturality R M g)

end oneIsoTorKerAux
