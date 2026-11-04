module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.ULift
public import Mathlib.Order.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Module.ULift

/-!
# Flat base change for `Tor`, and `Tor` commutes with filtered colimits

Let `R → R'` be a flat ring map of commutative rings and let `M`, `N` be `R`-modules. Then for
every `i` the base-change map
`Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism of `R'`-modules (Stacks 00M8). Here `Tor` is `CategoryTheory.Tor` on the
monoidal abelian category `ModuleCat R`, and base change is
`ModuleCat.extendScalars (algebraMap R R')`.

Let `(G i)` be a directed system of `R`-modules indexed by a nonempty directed preorder, and `N`
an `R`-module. Then `Tor_n^R(-, N)` sends the direct-limit colimit cocone of `(G i)` to a colimit
cocone: `Tor_n^R(colim_i G i, N) = colim_i Tor_n^R(G i, N)` (Stacks 0BNF).

## Main definitions

* `torBaseChangeIso`: the base-change isomorphism
  `Tor_i^R(M, N) ⊗_R R' ≅ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')` for flat `R'`.
* `torTensorComplex`: the functor tensoring a fixed chain complex of modules levelwise.
* `torFlipObjIsoTensorComplexHomology`: `Tor_n^R(-, N)` is the `n`-th homology of a projective
  resolution of `N` tensored with the argument.

## Main results

* `flat_base_change_tor`: flat base change for `Tor`.
* `tor_flip_preservesColimit_directLimit`: `Tor_n^R(-, N)` preserves direct limits.
* `tor_commutes_filtered_colimits`: `Tor` commutes with filtered colimits, with the ring, the
  index type, the modules and `N` in independent universes.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

/-- Base change of `R`-modules along `R → R'`, the functor `- ⊗_R R'`. -/
@[ega "III 6.1.1" "special case", sga "6 IV 2.6" "special case"]
noncomputable abbrev torBaseChange : ModuleCat.{0} R ⥤ ModuleCat.{0} R' :=
  ModuleCat.extendScalars (algebraMap R R')

/-- Base change is an additive functor. -/
noncomputable instance torBaseChange_additive :
    (torBaseChange (R := R) (R' := R')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).left_adjoint_additive

/-- When `R'` is flat over `R`, base change preserves finite limits. -/
noncomputable instance torBaseChange_preservesFiniteLimits [Module.Flat R R'] :
    Limits.PreservesFiniteLimits (torBaseChange (R := R) (R' := R')) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr ‹_›)

/-- When `R'` is flat over `R`, base change is exact, hence preserves homology. -/
@[ega "III 6.1.1" "special case", sga "3 VIB 11.0" "special case"]
noncomputable instance torBaseChange_preservesHomology [Module.Flat R R'] :
    (torBaseChange (R := R) (R' := R')).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Base change sends projective modules to projective modules. -/
@[ega "III 6.3.8" "Projectivity clause"]
noncomputable instance torBaseChange_preservesProjectives :
    (torBaseChange (R := R) (R' := R')).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R'))

/-- Base change commutes with tensoring by `M`:
`(M ⊗_R X) ⊗_R R' ≅ (M ⊗_R R') ⊗_{R'} (X ⊗_R R')`, naturally in `X`. -/
noncomputable def torBaseChangeTensorIso (M : ModuleCat.{0} R) :
    (MonoidalCategory.tensorLeft M) ⋙ torBaseChange (R := R) (R' := R') ≅
      torBaseChange (R := R) (R' := R') ⋙
        MonoidalCategory.tensorLeft ((torBaseChange (R := R) (R' := R')).obj M) :=
  NatIso.ofComponents
    (fun X => (asIso (Functor.LaxMonoidal.μ
      (ModuleCat.extendScalars (algebraMap R R')) M X)).symm)
    (by
      intro X Y f
      dsimp
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact (Functor.LaxMonoidal.μ_natural_right
        (ModuleCat.extendScalars (algebraMap R R')) M f).symm)

/-- For flat `R'`, base change commutes with homology: `H_n(K) ⊗_R R' ≅ H_n(K ⊗_R R')`. -/
noncomputable def torBaseChangeHomologyIso [Module.Flat R R']
    (K : HomologicalComplex (ModuleCat.{0} R) (ComplexShape.down ℕ)) (n : ℕ) :
    (torBaseChange (R := R) (R' := R')).obj (K.homology n) ≅
      (((torBaseChange (R := R) (R' := R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K).homology n :=
  (ShortComplex.mapHomologyIso (K.sc n) (torBaseChange (R := R) (R' := R'))).symm ≪≫
    HomologicalComplex.homologyMapIso
      (Iso.refl (((torBaseChange (R := R) (R' := R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K)) n

/-- The base-change isomorphism
`Tor_i^R(M, N) ⊗_R R' ≅ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')` for flat `R'`, computed on the chosen
projective resolution of `N`. -/
@[ega "III 6.3.9" "special case", ega "III 6.9.2" "special case"]
noncomputable def torBaseChangeIso [Module.Flat R R'] (i : ℕ) (M N : ModuleCat.{0} R) :
    (torBaseChange (R := R) (R' := R')).obj (((Tor (ModuleCat.{0} R) i).obj M).obj N) ≅
      ((Tor (ModuleCat.{0} R') i).obj ((torBaseChange (R := R) (R' := R')).obj M)).obj
        ((torBaseChange (R := R) (R' := R')).obj N) := by
  let P : ProjectiveResolution N := ProjectiveResolution.of N
  let cs := ComplexShape.down ℕ
  let T := MonoidalCategory.tensorLeft M
  let T' := MonoidalCategory.tensorLeft ((torBaseChange (R := R) (R' := R')).obj M)
  refine (torBaseChange (R := R) (R' := R')).mapIso (P.isoLeftDerivedObj T i) ≪≫ ?_
  refine torBaseChangeHomologyIso ((T.mapHomologicalComplex cs).obj P.complex) i ≪≫ ?_
  refine (HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (torBaseChangeTensorIso M) cs).app P.complex) i) ≪≫ ?_
  exact (((torBaseChange (R := R) (R' := R')).mapProjectiveResolution P).isoLeftDerivedObj T'
      i).symm

variable (R') in
/-- **Flat base change for Tor.** Let `R → R'` be a flat ring map of commutative rings and let
`M`, `N` be `R`-modules. Then for every `i` the base-change map
`(torBaseChangeIso i M N).hom : Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')`
is an isomorphism of `R'`-modules. -/
@[stacks 00M8]
theorem flat_base_change_tor [Module.Flat R R'] (i : ℕ) (M N : ModuleCat.{0} R) :
    IsIso (torBaseChangeIso (R' := R') i M N).hom :=
  inferInstance

/-! ### `Tor` commutes with filtered colimits -/

@[expose] public section

universe u v w x

open CategoryTheory CategoryTheory.Limits

/-- **Naturality in the functor variable of the projective-resolution presentation of a
left-derived functor.**  For a fixed projective resolution `P` of `X` and a natural
transformation `α : F ⟶ G`, the comparison isomorphisms
`P.isoLeftDerivedObj _ n : (·.leftDerived n).obj X ≅ Hₙ((·).mapHomologicalComplex.obj P.complex)`
intertwine `NatTrans.leftDerived α n` with the map induced by `α` on the homology of
`P.complex`. -/
theorem isoLeftDerivedObj_naturality_functor
    {C : Type*} [Category C] {D : Type*} [Category D] [Abelian C]
    [HasProjectiveResolutions C] [Abelian D] {X : C} (P : ProjectiveResolution X)
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    (NatTrans.leftDerived α n).app X ≫ (P.isoLeftDerivedObj G n).hom =
      (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) := by
  rw [P.leftDerived_app_eq α n, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

open MonoidalCategory in
/-- The functor `M ↦ M ⊗ Pc` from `R`-modules to chain complexes, tensoring a fixed chain
complex `Pc` levelwise. -/
@[ega "III 7.6.4" "partial"]
noncomputable def torTensorComplex {R : Type u} [CommRing R]
    (Pc : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := ((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)
    |>.obj Pc
  map {M M'} φ :=
    (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map φ)
      (ComplexShape.down ℕ)).app Pc
  map_id M := by ext; simp
  map_comp φ ψ := by ext; simp

open MonoidalCategory in
/-- In each homological degree `k`, `torTensorComplex Pc` is naturally isomorphic to
`- ⊗ Pc.X k`. -/
noncomputable def torTensorComplexEval {R : Type u} [CommRing R]
    (Pc : ChainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) :
    torTensorComplex Pc ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k ≅
      tensorRight (Pc.X k) :=
  NatIso.ofComponents (fun M => Iso.refl _)
    (fun _ => by simp [torTensorComplex, HomologicalComplex.eval])

/-- `torTensorComplex Pc` preserves colimits of any shape. -/
@[ega "0 4.1.5" "special case", sga "5 V 1.2.1" "special case"]
noncomputable instance torTensorComplex_preservesColimitsOfShape {R : Type u} [CommRing R]
    (Pc : ChainComplex (ModuleCat.{u} R) ℕ) {J : Type v} [Category J] :
    PreservesColimitsOfShape J (torTensorComplex Pc) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _
    fun k => preservesColimitsOfShape_of_natIso (torTensorComplexEval Pc k).symm

open MonoidalCategory in
/-- As a functor of `M`, `Tor_n^R(-, N) = (Tor n).flip.obj N` is naturally isomorphic to
`torTensorComplex P.complex ⋙ Hₙ`, the `n`-th homology of a projective resolution `P` of `N`
tensored with `M`. -/
noncomputable def torFlipObjIsoTensorComplexHomology {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (n : ℕ) (P : ProjectiveResolution N) :
    (CategoryTheory.Tor (ModuleCat.{u} R) n).flip.obj N ≅
      torTensorComplex P.complex ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n :=
  NatIso.ofComponents
    (fun M => P.isoLeftDerivedObj ((tensoringLeft (ModuleCat.{u} R)).obj M) n)
    (by
      intro M M' φ
      dsimp only [Functor.comp_map, torTensorComplex]
      exact isoLeftDerivedObj_naturality_functor P ((tensoringLeft (ModuleCat.{u} R)).map φ) n)

/-- The functor `shortComplexFunctor` in degree `n` on chain complexes of `R`-modules preserves
colimits of any shape. -/
noncomputable instance shortComplexFunctor_preservesColimitsOfShape
    {R : Type u} [CommRing R] {ι : Type u} [Category ι] (n : ℕ) :
    PreservesColimitsOfShape ι
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n) := by
  refine ⟨fun {K} => preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K) ?_⟩
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ)
        ((ComplexShape.down ℕ).prev n))
      (colimit.isColimit K)
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n) (colimit.isColimit K)
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ)
        ((ComplexShape.down ℕ).next n))
      (colimit.isColimit K)

-- needed: `shortComplexHomologyFunctorIso`'s components are the required maps only after
-- unfolding `mapHomologyIso`/`eval` past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- For a diagram `K : ι ⥤ ShortComplex (ModuleCat R)`, the pointwise homology functor applied to
`K` is naturally isomorphic to the homology (computed in the functor category) of the corresponding
short complex `S = e.inverse.obj K` of functors. -/
noncomputable def shortComplexHomologyFunctorIso
    {R : Type u} [CommRing R] {ι : Type u} [Category ι] (K : ι ⥤ ShortComplex (ModuleCat.{u} R)) :
    K ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)
      ≅ ((ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K).homology :=
  NatIso.ofComponents
    (fun j => ((ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K).mapHomologyIso
      ((evaluation ι (ModuleCat.{u} R)).obj j))
    (by
      intro i j f
      have hK : ShortComplex.homologyMap (K.map f)
          = ShortComplex.homologyMap
              (((ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K).mapNatTrans
                ((evaluation ι (ModuleCat.{u} R)).map f)) := rfl
      simp only [Functor.comp_map, ShortComplex.homologyFunctor_map]
      rw [hK, ((ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj
          K).homologyMap_mapNatTrans
        ((evaluation ι (ModuleCat.{u} R)).map f)]
      simp)

-- needed: `shortComplexColimCocone`'s cocone fields typecheck only with the componentwise
-- colimit unfolded past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- The cocone on `K : ι ⥤ ShortComplex (ModuleCat R)` whose apex is the componentwise colimit
`S.map colim`, where `S = e.inverse.obj K`, and whose legs are the colimit injections of the
`K ⋙ πᵢ`. -/
noncomputable def shortComplexColimCocone
    {R : Type u} [CommRing R] {ι : Type u} [Category ι] [HasColimitsOfShape ι (ModuleCat.{u} R)]
    (K : ι ⥤ ShortComplex (ModuleCat.{u} R)) :
    Cocone K where
  pt := (ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K |>.map
    (colim (J := ι) (C := ModuleCat.{u} R))
  ι :=
    { app := fun j => ShortComplex.homMk (colimit.ι (K ⋙ ShortComplex.π₁) j)
        (colimit.ι (K ⋙ ShortComplex.π₂) j) (colimit.ι (K ⋙ ShortComplex.π₃) j)
        (by dsimp [ShortComplex.map]; rw [ι_colimMap]; rfl)
        (by dsimp [ShortComplex.map]; rw [ι_colimMap]; rfl)
      naturality := by
        intro i j f
        refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
        · simpa using colimit.w (K ⋙ ShortComplex.π₁) f
        · simpa using colimit.w (K ⋙ ShortComplex.π₂) f
        · simpa using colimit.w (K ⋙ ShortComplex.π₃) f }

/-- `shortComplexColimCocone K` is a colimit cocone. -/
noncomputable def shortComplexColimIsColimit
    {R : Type u} [CommRing R] {ι : Type u} [Category ι] [HasColimitsOfShape ι (ModuleCat.{u} R)]
    (K : ι ⥤ ShortComplex (ModuleCat.{u} R)) :
    IsColimit (shortComplexColimCocone K) :=
  ShortComplex.isColimitOfIsColimitπ _
    (colimit.isColimit (K ⋙ ShortComplex.π₁))
    (colimit.isColimit (K ⋙ ShortComplex.π₂))
    (colimit.isColimit (K ⋙ ShortComplex.π₃))

-- needed: `shortComplexHomologyFunctor_preservesColimitsOfShape` assembles the instance from
-- the two cocone defs above, needing the same defeq past the default transparency
set_option backward.isDefEq.respectTransparency false in
/-- The homology functor on `ShortComplex (ModuleCat R)` preserves colimits indexed by a nonempty
directed preorder `ι`: homology of short complexes of `R`-modules commutes with such colimits. -/
@[ega "0 11.2.4" "special case",
  ega "0 12.4.1" "special case",
  ega "III 1.1.6" "more general",
  sga "4 XVII 5.5.6.3" "special case"]
noncomputable instance shortComplexHomologyFunctor_preservesColimitsOfShape
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] :
    PreservesColimitsOfShape ι (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  have hPH : (colim (J := ι) (C := ModuleCat.{u} R)).PreservesHomology :=
    { preservesKernels := fun {X Y} f => inferInstance
      preservesCokernels := fun {X Y} f => inferInstance }
  refine ⟨fun {K} => ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone
    (t := shortComplexColimCocone K) (shortComplexColimIsColimit K)
  refine IsColimit.ofIsoColimit
    (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)))
    (Cocone.ext
      (HasColimit.isoOfNatIso (shortComplexHomologyFunctorIso K) ≪≫
        (((ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K).mapHomologyIso
          (colim (J := ι) (C := ModuleCat.{u} R))).symm) ?_)
  intro j
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, Iso.trans_hom,
    HasColimit.isoOfNatIso_ι_hom_assoc, shortComplexHomologyFunctorIso,
    NatIso.ofComponents_hom_app]
  set S := (ShortComplex.functorEquivalence ι (ModuleCat.{u} R)).inverse.obj K
  let α : ((evaluation ι (ModuleCat.{u} R)).obj j) ⟶ (colim (J := ι) (C := ModuleCat.{u} R)) :=
    { app := fun F => colimit.ι F j, naturality := fun _ _ _ => by simp }
  rw [ShortComplex.homologyFunctor_map, Iso.symm_hom,
    ← ShortComplex.homologyMap_mapNatTrans S α]
  have hmaps : S.mapNatTrans α = (shortComplexColimCocone K).ι.app j := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;>
      simp only [shortComplexColimCocone, S, ShortComplex.functorEquivalence,
        ShortComplex.mapNatTrans, α, ShortComplex.homMk_τ₁, ShortComplex.homMk_τ₂,
        ShortComplex.homMk_τ₃] <;> rfl
  rw [hmaps]

/-- The homology functor on chain complexes of `R`-modules preserves colimits indexed by a
nonempty directed preorder. -/
theorem homologyFunctor_preservesColimitsOfShape_of_isDirected
    {R : Type u} [CommRing R] {ι : Type u}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (n : ℕ) :
    PreservesColimitsOfShape ι
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n) := by
  have : PreservesColimitsOfShape ι
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
        ShortComplex.homologyFunctor (ModuleCat.{u} R)) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} R) (ComplexShape.down ℕ) n).symm

/-- `Tor_n^R(-, N)` sends the direct-limit colimit cocone of a directed system to a colimit
cocone. -/
@[ega "III 6.3.12" "special case", ega "III 6.3.6" "special case", ega "III 6.5.6" "special case"]
theorem tor_flip_preservesColimit_directLimit
    {R : Type u} [CommRing R]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (N : ModuleCat.{u} R) (n : ℕ) :
    PreservesColimit (ModuleCat.directLimitDiagram G f)
      ((CategoryTheory.Tor (ModuleCat.{u} R) n).flip.obj N) := by
  have := homologyFunctor_preservesColimitsOfShape_of_isDirected (R := R) (ι := ι) n
  exact preservesColimit_of_natIso _
    (torFlipObjIsoTensorComplexHomology N n (ProjectiveResolution.of N)).symm

/-! ### Universe lifting

`CategoryTheory.Tor (ModuleCat.{s} S)` requires `S : Type s`, and `ModuleCat.directLimitDiagram`
puts the index type and the modules in one universe, so the statement with independent universes
is about the canonical `ULift`s into `max u v w x`.
-/

/-- Transition maps of the canonical `ULift` of a directed system of `R`-modules into the
universe `max u v w x`: the index type `ι : Type v` becomes `ULift.{max u w x, v} ι`, each module
`G i : Type w` becomes `ULift.{max u v x, w} (G i)`, and the scalars `R : Type u` become
`ULift.{max v w x, u} R`. -/
def torULiftTransition {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
    (G : ι → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (i j : ULift.{max u w x, v} ι) (h : i ≤ j) :
    ULift.{max u v x, w} (G i.down) →ₗ[ULift.{max v w x, u} R]
      ULift.{max u v x, w} (G j.down) where
  toFun y := ULift.up (f i.down j.down h y.down)
  map_add' y z := congrArg ULift.up (map_add (f i.down j.down h) y.down z.down)
  map_smul' c y := congrArg ULift.up (map_smul (f i.down j.down h) c.down y.down)

/-- The canonical `ULift` of a directed system of `R`-modules is again a directed system. -/
instance torULiftDirectedSystem {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
    (G : ι → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)] :
    DirectedSystem (fun i : ULift.{max u w x, v} ι => ULift.{max u v x, w} (G i.down))
      (fun i j h => torULiftTransition.{u, v, w, x} G f i j h) where
  map_self _ y := congrArg ULift.up (DirectedSystem.map_self' f y.down)
  map_map _ _ _ hij hjk y := congrArg ULift.up (DirectedSystem.map_map' f hij hjk y.down)

/-- **Tor commutes with filtered colimits.** Applying `Tor_n^R(-, N)` to the direct-limit
colimit cocone of a directed system `(G i)` of `R`-modules yields again a colimit cocone, i.e. the
canonical map `colim_i Tor_n^R(G i, N) → Tor_n^R(colim_i G i, N)` is an isomorphism.

The ring `R : Type u`, the index type `ι : Type v`, the modules `G : ι → Type w` and the second
argument `N : ModuleCat.{x} R` live in four independent universes, and the conclusion is stated
about their canonical `ULift`s into `max u v w x`. -/
@[stacks 0BNF,
  ega "III 6.3.12" "special case",
  ega "III 6.3.6" "special case",
  ega "III 6.5.6" "special case"]
theorem tor_commutes_filtered_colimits
    {R : Type u} [CommRing R]
    {ι : Type v} [DecidableEq ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (N : ModuleCat.{x} R) (n : ℕ) :
    Nonempty (CategoryTheory.Limits.IsColimit
      (((CategoryTheory.Tor (ModuleCat.{max u v w x} (ULift.{max v w x, u} R)) n).flip.obj
            (ModuleCat.of (ULift.{max v w x, u} R) (ULift.{max u v w, x} N))).mapCocone
        (ModuleCat.directLimitCocone
          (fun i : ULift.{max u w x, v} ι => ULift.{max u v x, w} (G i.down))
          (torULiftTransition.{u, v, w, x} G f)))) := by
  have : IsDirected (ULift.{max u w x, v} ι) (· ≤ ·) :=
    ⟨fun a b =>
      let ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.down b.down
      ⟨ULift.up c, hac, hbc⟩⟩
  have := tor_flip_preservesColimit_directLimit
    (fun i : ULift.{max u w x, v} ι => ULift.{max u v x, w} (G i.down))
    (torULiftTransition.{u, v, w, x} G f)
    (ModuleCat.of (ULift.{max v w x, u} R) (ULift.{max u v w, x} N)) n
  exact ⟨isColimitOfPreserves _ (ModuleCat.directLimitIsColimit _ _)⟩

/-- `tor_commutes_filtered_colimits` with the ring, the index type, the modules and `N` in one
universe `u`. -/
private theorem tor_commutes_filtered_colimits_single_universe
    {R : Type u} [CommRing R]
    {ι : Type u} [DecidableEq ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (N : ModuleCat.{u} R) (n : ℕ) :
    Nonempty (CategoryTheory.Limits.IsColimit
      (((CategoryTheory.Tor (ModuleCat.{u} (ULift.{u, u} R)) n).flip.obj
            (ModuleCat.of (ULift.{u, u} R) (ULift.{u, u} N))).mapCocone
        (ModuleCat.directLimitCocone
          (fun i : ULift.{u, u} ι => ULift.{u, u} (G i.down))
          (torULiftTransition.{u, u, u, u} G f)))) :=
  tor_commutes_filtered_colimits G f N n
