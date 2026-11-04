module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechComparison

/-!
# The extended alternating Čech complex is the colimit of the Koszul complexes

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. This file proves
that the extended alternating Čech complex

`𝒪 → ∏_{i₀} 𝒪_{f_{i₀}} → ∏_{i₀ < i₁} 𝒪_{f_{i₀}f_{i₁}} → ⋯ → 𝒪_{f_1 ⋯ f_r}`

is the colimit, in the category of cochain complexes of sheaves of `𝒪`-modules, of the
sequential diagram of the Koszul complexes `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` along the maps
between successive powers. This is [Stacks, Tag 0913] for sheaves of modules on a site.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulCechComplexMap`: the comparison
  `K(𝒪, f^{n+1}) ⟶ Č(f)` of complexes, induced by
  `AlgebraicGeometry.RingedSite.koszulCechTrans`.
* `AlgebraicGeometry.RingedSite.koszulCechComplexCocone`: the cocone on `Č(f)` over the
  sequential diagram `AlgebraicGeometry.RingedSite.koszulPowerSystem` of Koszul complexes.

## Main results

* `AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`: **the extended alternating
  Čech complex is the colimit of the Koszul complexes on the positive powers of
  `f_1, …, f_r`.**

## Implementation notes

Colimits of cochain complexes are computed degreewise, by
`HomologicalComplex.isColimitOfEval`, and in degree `p` both complexes are a finite product
indexed by the subsets of `{1, …, r}` of cardinality `p`: the Koszul complex has `𝒪` in every
factor and the Čech complex has `𝒪_{f_S}`. So what has to be proved in each degree is that a
finite product of colimit cocones is a colimit cocone, which in a preadditive category it is,
a finite product being also a coproduct there.

That last point is used through three facts about a product over a finite index type in a
preadditive category, proved here from `CategoryTheory.Limits.Pi.lift` and
`CategoryTheory.Limits.Pi.π` alone rather than through `CategoryTheory.Limits.biproduct` and
`CategoryTheory.Limits.biproduct.isoProduct`, so that no transport along that comparison
appears: the inclusion of a factor, the identity `∑_A π_A ≫ δ_A = 𝟙` and the compatibility of
the inclusions with a product of morphisms.

The descent is assembled from the subsetwise descents as `∑_A π_A ≫ desc_A`, and both its
defining property and its uniqueness are telescoped with that identity. As in
`KoszulCechComparison.lean` the colimit is proved by exhibiting the descent, its defining
property and its uniqueness, rather than by comparing the evaluation at `p` of the sequential
diagram with a sequential diagram of the factors: `CategoryTheory.Functor.ofSequence` builds
the morphism attached to a general `i ≤ j` by recursion, so those two are not the same term.

The universes are the diagonal `RingedSite.{u, u, u}` with coefficient universe `u`, as in
`KoszulCechComparison.lean`.

[Stacks, Tag 0913] is stated in More on Algebra for the Koszul complexes of a finite sequence
of elements of a ring; that statement is `Cech.cechComplex_isColimit_koszulPowerComplexes` of
`StacksFrontier/RingTheory/Cech/KoszulColimit.lean`, and
`AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone` is its ringed-site analogue. By
[Stacks, Tag 0949] it gives the homotopy colimit presentation in `D(𝒪)`
`AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem` of
`KoszulCechHomotopyColimit.lean`, which is the input `hcolim` of the formula of
[Stacks, Tag 0A0E].

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ## Two general lemmas -/

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type u} [Category 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]
  {F G H : Finset (Fin r) ⥤ 𝒜}

omit [Preadditive 𝒜] in
/-- The degreewise maps of alternating Čech complexes induced by two morphisms of systems
compose. -/
theorem mapX_comp (α : F ⟶ G) (β : G ⟶ H) (p : ℤ) :
    mapX α p ≫ mapX β p = mapX (α ≫ β) p :=
  mapX_comp_mapX α β p

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative

section Pi

variable {𝒜 : Type u} [Category 𝒜] [Preadditive 𝒜] {ι : Type} [DecidableEq ι]
  (g : ι → 𝒜) [HasProduct g]

/-- The inclusion of the factor indexed by `A` into a product over a finite index type: the
identity in that factor and zero in the others. -/
private def piDelta (A : ι) : g A ⟶ ∏ᶜ g :=
  Pi.lift fun B => if h : A = B then eqToHom (congrArg g h) else 0

private theorem piDelta_comp_π (A B : ι) :
    piDelta g A ≫ Pi.π g B = if h : A = B then eqToHom (congrArg g h) else 0 :=
  Pi.lift_π _ _

private theorem piDelta_comp_π_self (A : ι) : piDelta g A ≫ Pi.π g A = 𝟙 (g A) := by
  rw [piDelta_comp_π]
  simp

private theorem piDelta_comp_π_of_ne {A B : ι} (h : A ≠ B) : piDelta g A ≫ Pi.π g B = 0 := by
  rw [piDelta_comp_π]
  simp [h]

/-- **A product over a finite index type in a preadditive category is a coproduct**: the sum
over the index type of the projection followed by the inclusion is the identity. -/
private theorem pi_total [Fintype ι] : ∑ A : ι, Pi.π g A ≫ piDelta g A = 𝟙 (∏ᶜ g) := by
  refine Pi.hom_ext _ _ fun B => ?_
  rw [Preadditive.sum_comp, Category.id_comp]
  refine (Finset.sum_eq_single_of_mem B (Finset.mem_univ B) ?_).trans ?_
  · intro A _ hAB
    rw [Category.assoc, piDelta_comp_π_of_ne g hAB, comp_zero]
  · rw [Category.assoc, piDelta_comp_π_self, Category.comp_id]

/-- The inclusions of the factors are compatible with a product of morphisms. -/
private theorem piDelta_comp_map {g' : ι → 𝒜} [HasProduct g'] (q : ∀ i, g i ⟶ g' i) (A : ι) :
    piDelta g A ≫ Limits.Pi.map q = q A ≫ piDelta g' A := by
  refine Pi.hom_ext _ _ fun B => ?_
  rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, piDelta_comp_π, Category.assoc,
    piDelta_comp_π]
  by_cases h : A = B
  · subst h
    simp
  · simp [h]

end Pi

/-! ## The comparison of complexes -/

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The comparison of the Koszul complex on the `(n+1)`-st powers of `f_1, …, f_r` with the
extended alternating Čech complex**, induced by
`AlgebraicGeometry.RingedSite.koszulCechTrans`: in the factor indexed by `S` it is the
canonical map `𝒪 ⟶ 𝒪_{f_S}` divided by `f_S^{n+1}`. -/
def koszulCechComplexMap (n : ℕ) :
    koszulPowerComplex X f n ⟶ extendedAlternatingCech X f :=
  CategoryTheory.AlternatingCech.map (koszulCechTrans X f n)

/-- In degree `p`, the comparison of the Koszul complex with the extended alternating Čech complex
is the product of the factorwise comparison maps. -/
@[simp]
theorem koszulCechComplexMap_f (n : ℕ) (p : ℤ) :
    (koszulCechComplexMap X f n).f p =
      CategoryTheory.AlternatingCech.mapX (koszulCechTrans X f n) p :=
  rfl

/-- The map between successive Koszul powers followed by the comparison with the Čech complex
is the comparison with the Čech complex. -/
theorem koszulPowerComplexMap_comp_koszulCechComplexMap (n : ℕ) :
    koszulPowerComplexMap X f n ≫ koszulCechComplexMap X f (n + 1) =
      koszulCechComplexMap X f n := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  show CategoryTheory.AlternatingCech.mapX (koszulPowerTrans X f n) p ≫
      CategoryTheory.AlternatingCech.mapX (koszulCechTrans X f (n + 1)) p =
    CategoryTheory.AlternatingCech.mapX (koszulCechTrans X f n) p
  rw [CategoryTheory.AlternatingCech.mapX_comp, koszulPowerTrans_comp_koszulCechTrans]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The transition map from the `n`-th to the `(n+1)`-st term of the sequential diagram of Koszul
complexes is the map between successive Koszul powers. -/
theorem koszulPowerSystem_map_succ (n : ℕ) :
    (koszulPowerSystem X f).map (homOfLE (n.le_add_right 1)) = koszulPowerComplexMap X f n :=
  Functor.ofSequence_map_homOfLE_succ _ n

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- In degree `p`, the transition map from the `n`-th to the `(n+1)`-st term of the sequential
diagram of Koszul complexes is the product of the factorwise maps between successive powers. -/
theorem koszulPowerSystem_map_succ_f (n : ℕ) (p : ℤ) :
    ((koszulPowerSystem X f).map (homOfLE (n.le_add_right 1))).f p =
      CategoryTheory.AlternatingCech.mapX (koszulPowerTrans X f n) p := by
  rw [koszulPowerSystem_map_succ, koszulPowerComplexMap]
  rfl

/-- **The cocone on the extended alternating Čech complex** over the sequential diagram of the
Koszul complexes on the positive powers of `f_1, …, f_r`. -/
def koszulCechComplexCocone : Cocone (koszulPowerSystem X f) where
  pt := extendedAlternatingCech X f
  ι := NatTrans.ofSequence (koszulCechComplexMap X f) (fun n => by
    rw [koszulPowerSystem_map_succ]
    exact (koszulPowerComplexMap_comp_koszulCechComplexMap X f n).trans
      (Category.comp_id _).symm)

/-- The `n`-th leg of the cocone on the extended alternating Čech complex is the comparison of
the Koszul complex on the `(n+1)`-st powers with the extended alternating Čech complex. -/
@[simp]
theorem koszulCechComplexCocone_ι_app (n : ℕ) :
    (koszulCechComplexCocone X f).ι.app n = koszulCechComplexMap X f n :=
  rfl

/-! ## The degreewise colimit -/

section Term

open CategoryTheory.AlternatingCech

variable (p : ℤ)

/-- The inclusion of the factor indexed by `A` into the degree-`p` term of the Koszul complex
on the `(n+1)`-st powers. -/
private def koszulDelta (n : ℕ) (A : Idx r p) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      term (koszulPowerFunctor X f n) p :=
  piDelta (fun S : Idx r p => (koszulPowerFunctor X f n).obj S.1) A

/-- The inclusion of the factor indexed by `A` into the degree-`p` term of the extended
alternating Čech complex. -/
private def cechDelta (A : Idx r p) :
    awayModule X (prodGlobalSection f A.1) ⟶ term (awayLocalizationFunctor X f) p :=
  piDelta (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A

omit [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem koszulDelta_comp_mapX_koszulPowerTrans (n : ℕ) (A : Idx r p) :
    koszulDelta X f p n A ≫ mapX (koszulPowerTrans X f n) p =
      koszulScalar X f (koszulIndicator A.1 1) ≫ koszulDelta X f p (n + 1) A :=
  piDelta_comp_map _ (fun S : Idx r p => (koszulPowerTrans X f n).app S.1) A

private theorem koszulDelta_comp_mapX_koszulCechTrans (n : ℕ) (A : Idx r p) :
    koszulDelta X f p n A ≫ mapX (koszulCechTrans X f n) p =
      awayModuleCoconeι X (prodGlobalSection f A.1) (n + 1) ≫ cechDelta X f p A :=
  piDelta_comp_map _ (fun S : Idx r p => (koszulCechTrans X f n).app S.1) A

omit [HasWeakSheafify X.J CommRingCat.{u}] in
private theorem koszul_pi_total (n : ℕ) :
    ∑ A : Idx r p, Pi.π (fun S : Idx r p => (koszulPowerFunctor X f n).obj S.1) A ≫
        koszulDelta X f p n A = 𝟙 (term (koszulPowerFunctor X f n) p) :=
  pi_total (fun S : Idx r p => (koszulPowerFunctor X f n).obj S.1)

private theorem cech_pi_total :
    ∑ A : Idx r p, Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫
        cechDelta X f p A = 𝟙 (term (awayLocalizationFunctor X f) p) :=
  pi_total (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1)

variable (c : Cocone (koszulPowerSystem X f ⋙
  HomologicalComplex.eval (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) p))

/-- The cocone over `𝒪 --f_A--> 𝒪 --f_A--> ⋯` induced at the factor `A` by a cocone over the
degree-`p` terms of the Koszul complexes. -/
private def termDescCocone (A : Idx r p) :
    Cocone (awaySequence X (koszulScalar X f (koszulIndicator A.1 1))) where
  pt := c.pt
  ι := NatTrans.ofSequence (fun n => koszulDelta X f p n A ≫ c.ι.app n) (fun n => by
    have hd : koszulScalar X f (koszulIndicator A.1 1) ≫ koszulDelta X f p (n + 1) A =
        koszulDelta X f p n A ≫
          (koszulPowerSystem X f ⋙ HomologicalComplex.eval
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) p).map
              (homOfLE (n.le_add_right 1)) := by
      rw [Functor.comp_map, HomologicalComplex.eval_map, koszulPowerSystem_map_succ_f]
      exact (koszulDelta_comp_mapX_koszulPowerTrans X f p n A).symm
    rw [awaySequence_map_succ]
    refine Eq.trans ?_ (Category.comp_id _).symm
    calc koszulScalar X f (koszulIndicator A.1 1) ≫
            koszulDelta X f p (n + 1) A ≫ c.ι.app (n + 1)
        = (koszulScalar X f (koszulIndicator A.1 1) ≫ koszulDelta X f p (n + 1) A) ≫
            c.ι.app (n + 1) := (Category.assoc _ _ _).symm
      _ = (koszulDelta X f p n A ≫
            (koszulPowerSystem X f ⋙ HomologicalComplex.eval
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                (ComplexShape.up ℤ) p).map
                (homOfLE (n.le_add_right 1))) ≫ c.ι.app (n + 1) :=
          congrArg (fun k => k ≫ c.ι.app (n + 1)) hd
      _ = koszulDelta X f p n A ≫
            ((koszulPowerSystem X f ⋙ HomologicalComplex.eval
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                (ComplexShape.up ℤ) p).map
                (homOfLE (n.le_add_right 1)) ≫ c.ι.app (n + 1)) := Category.assoc _ _ _
      _ = koszulDelta X f p n A ≫ c.ι.app n :=
          congrArg (fun k => koszulDelta X f p n A ≫ k)
            (c.w (homOfLE (n.le_add_right 1))))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
@[simp]
private theorem termDescCocone_ι_app (A : Idx r p) (n : ℕ) :
    (termDescCocone X f p c A).ι.app n = koszulDelta X f p n A ≫ c.ι.app n :=
  rfl

/-- The descent of a cocone over the degree-`p` terms, factor by factor. -/
private def termDescApp (A : Idx r p) : (awayLocalizationFunctor X f).obj A.1 ⟶ c.pt :=
  (isColimitAwayModuleShiftCocone X (prodGlobalSection f A.1)
      (koszulScalar X f (koszulIndicator A.1 1))
      (koszulScalar_koszulIndicator_one_app_apply X f A.1)).desc (termDescCocone X f p c A)

private theorem termDescApp_fac (A : Idx r p) (n : ℕ) :
    awayModuleCoconeι X (prodGlobalSection f A.1) (n + 1) ≫ termDescApp X f p c A =
      koszulDelta X f p n A ≫ c.ι.app n :=
  (isColimitAwayModuleShiftCocone X (prodGlobalSection f A.1)
      (koszulScalar X f (koszulIndicator A.1 1))
      (koszulScalar_koszulIndicator_one_app_apply X f A.1)).fac
    (termDescCocone X f p c A) n

/-- The descent of a cocone over the degree-`p` terms: the sum over the subsets of cardinality
`p` of the projection followed by the descent at that factor. -/
private def termDesc : term (awayLocalizationFunctor X f) p ⟶ c.pt :=
  ∑ A : Idx r p, Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫
    termDescApp X f p c A

private theorem termDesc_fac (n : ℕ) :
    mapX (koszulCechTrans X f n) p ≫ termDesc X f p c = c.ι.app n := by
  have step : ∀ A : Idx r p, mapX (koszulCechTrans X f n) p ≫
      (Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫
        termDescApp X f p c A) =
      (Pi.π (fun S : Idx r p => (koszulPowerFunctor X f n).obj S.1) A ≫
        koszulDelta X f p n A) ≫ c.ι.app n := by
    intro A
    have hfac : (koszulCechTrans X f n).app A.1 ≫ termDescApp X f p c A =
        koszulDelta X f p n A ≫ c.ι.app n := termDescApp_fac X f p c A n
    rw [← Category.assoc, mapX_comp_pi, Category.assoc, hfac]
    exact (Category.assoc _ _ _).symm
  rw [termDesc, Preadditive.comp_sum, Finset.sum_congr rfl (fun A _ => step A),
    ← Preadditive.sum_comp Finset.univ
      (fun A : Idx r p => Pi.π (fun S : Idx r p => (koszulPowerFunctor X f n).obj S.1) A ≫
        koszulDelta X f p n A) (c.ι.app n),
    koszul_pi_total]
  exact Category.id_comp _

private theorem termDesc_uniq (m : term (awayLocalizationFunctor X f) p ⟶ c.pt)
    (hm : ∀ n : ℕ, mapX (koszulCechTrans X f n) p ≫ m = c.ι.app n) :
    m = termDesc X f p c := by
  have hA : ∀ A : Idx r p, cechDelta X f p A ≫ m = termDescApp X f p c A := by
    intro A
    refine (isColimitAwayModuleShiftCocone X (prodGlobalSection f A.1)
      (koszulScalar X f (koszulIndicator A.1 1))
      (koszulScalar_koszulIndicator_one_app_apply X f A.1)).hom_ext fun n => ?_
    show awayModuleCoconeι X (prodGlobalSection f A.1) (n + 1) ≫
        cechDelta X f p A ≫ m =
      awayModuleCoconeι X (prodGlobalSection f A.1) (n + 1) ≫ termDescApp X f p c A
    rw [← Category.assoc, ← koszulDelta_comp_mapX_koszulCechTrans, Category.assoc, hm,
      termDescApp_fac]
  calc m = 𝟙 (term (awayLocalizationFunctor X f) p) ≫ m := (Category.id_comp _).symm
    _ = (∑ A : Idx r p, Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫
          cechDelta X f p A) ≫ m := by rw [cech_pi_total]
    _ = ∑ A : Idx r p, Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫
          cechDelta X f p A ≫ m := by
        rw [Preadditive.sum_comp]
        exact Finset.sum_congr rfl fun A _ => Category.assoc _ _ _
    _ = termDesc X f p c := by
        rw [termDesc]
        exact Finset.sum_congr rfl fun A _ => congrArg (fun k =>
          Pi.π (fun S : Idx r p => (awayLocalizationFunctor X f).obj S.1) A ≫ k) (hA A)

/-- **The degree-`p` term of the Čech complex is the colimit of the degree-`p` terms of the
Koszul complexes.** A finite product is a coproduct in a preadditive category, so the descent
is the sum of the descents at the factors. -/
private def isColimitTermCocone :
    IsColimit ((HomologicalComplex.eval
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) p).mapCocone (koszulCechComplexCocone X f)) where
  desc c := termDesc X f p c
  fac c n := termDesc_fac X f p c n
  uniq c m hm := termDesc_uniq X f p c m hm

end Term

/-- **The extended alternating Čech complex of `f_1, …, f_r` is the colimit of the Koszul
complexes on the positive powers of `f_1, …, f_r`**, along the maps between successive powers.

This is [Stacks, Tag 0913] for sheaves of modules on a ringed site. Colimits of cochain
complexes are computed degreewise, and in degree `p` the statement is that the finite product
over the subsets of cardinality `p` of the colimits `𝒪_{f_S}` of `AwayColimit.lean` is the
colimit of the products of the `𝒪`, which holds because a finite product is a coproduct in a
preadditive category. -/
@[no_expose]
def isColimitKoszulCechComplexCocone : IsColimit (koszulCechComplexCocone X f) :=
  HomologicalComplex.isColimitOfEval _ _ fun p => isColimitTermCocone X f p

end AlgebraicGeometry.RingedSite

end
