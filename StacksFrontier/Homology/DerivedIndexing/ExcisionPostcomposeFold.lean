module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.Homology.DerivedCategory.MateDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedPullbackBaseChangeDegreewise

/-!
# The derived excision of a composite is the base change folded into the derived excision

Let `w : 𝒜 ⥤ 𝒞` and `w' : 𝒜' ⥤ 𝒞'` be additive, let `P : 𝒞 ⥤ 𝒜` and `P' : 𝒞' ⥤ 𝒜'` be exact —
the two direct images from a closed subset in the motivating instance — and let `F : 𝒜 ⥤ 𝒜'` and
`G : 𝒞 ⥤ 𝒞'` be exact.  Suppose given

* a degree-zero excision `δ : w ⋙ G ⟶ F ⋙ w'` for the inner functors, and
* a base change `θ : P ⋙ F ≅ G ⋙ P'` for the square of the direct images.

Then the degree-zero excision for the **composites** `w ⋙ P` and `w' ⋙ P'` is `δ` with `θ`
folded in, `foldZero`; and if `Rw` with unit `α` and `Rw'` with unit `α'` are total right derived
functors of `w` and `w'`, so that `Rw ⋙ P.mapDerivedCategory` and `Rw' ⋙ P'.mapDerivedCategory`
are total right derived functors of the composites, the comparison of the composites that the
uniqueness of right derived functors produces from `foldZero` is the comparison it produces from
`δ` with the **derived** 2-square `θ.mapDerivedCategory` folded in.

That is `eq_foldDerived`, and it is the step that carries the derived excision of
[Stacks, Tag 0G78] — which is built at the "on the closed subset" spelling of `R𝓗_Z` and then
pushed forward — onto the endofunctor spelling in which the classical excision of
[Stacks, Tag 0G87]'s square lives.

## Main definitions

* `Stacks.DerivedFunctor.foldZero`: the degree-zero fold-in, `(w ⋙ P) ⋙ F ⟶ F ⋙ (w' ⋙ P')`.
* `Stacks.DerivedFunctor.foldDerived`: the derived fold-in,
  `(Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory ⟶
   F.mapDerivedCategory ⋙ (Rw' ⋙ P'.mapDerivedCategory)`.

## Main results

* `Stacks.DerivedFunctor.foldZero_mapHomotopyCategory_app`: the degree-zero fold-in read on the
  homotopy category splits into the degreewise base change and `P'` applied to the degreewise
  `δ`.
* `Stacks.DerivedFunctor.foldDerived_fac`: **the factorization transports.**
* `Stacks.DerivedFunctor.eq_foldDerived`: **the fold-in is the only comparison with that
  factorization.**

## Implementation notes

**Why the statements are about natural transformations and not isomorphisms.**  Nothing here
needs `δ`, `Ψ` or `Θ` to be invertible; invertibility of the fold-in is a consequence of
invertibility of its two factors at the use site, and leaving it out keeps the hypothesis `hΨ` in
the shape `CategoryTheory.Functor.rightDerivedNatTrans_fac` produces it.

**Every chase is a helper at a variable category** with the objects implicit and the morphisms
explicit, applied by `exact`: at the concrete derived categories the spellings
`(w ⋙ P).mapHomotopyCategory c` and `w.mapHomotopyCategory c ⋙ P.mapHomotopyCategory c` of one
object are definitionally but not syntactically equal, so a `rw` whose motive crosses them is not
type-correct — `Functor.map_comp` cannot even be rewritten with, which is why `fold_chase`
carries the composite `a23` and its factorization as data.

**No `@[stacks ...]` attribute is attached**: this is a passage between two spellings of one
construction, not the statement of a tag.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace Stacks.DerivedFunctor

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
  {A' : Type uB} [Category.{vB} A'] [Abelian A'] [EnoughInjectives A']
    [HasDerivedCategory.{wB} A']
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {C' : Type uD} [Category.{vD} C'] [Abelian C'] [HasDerivedCategory.{wD} C']
  (w : A ⥤ C) [w.Additive] (w' : A' ⥤ C') [w'.Additive]
  (P : C ⥤ A) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (P' : C' ⥤ A') [P'.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  (F : A ⥤ A') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (δ : w ⋙ G ⟶ F ⋙ w') (θ : TwoSquare P G F P')

/-- **The degree-zero fold-in.**  From the base change `θ : P ⋙ F ≅ G ⋙ P'` of the square and
the degree-zero excision `δ : w ⋙ G ⟶ F ⋙ w'` on the inner functors, the degree-zero excision
for the composites `w ⋙ P` and `w' ⋙ P'`:

`(w ⋙ P) ⋙ F ⟶ F ⋙ (w' ⋙ P')`.

This is the shape of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafPushforwardPullbackNatIso` in degree
zero: four associators and two whiskerings, and no further mathematics. -/
def foldZero : (w ⋙ P) ⋙ F ⟶ F ⋙ (w' ⋙ P') :=
  (Functor.associator w P F).hom ≫ Functor.whiskerLeft w θ.natTrans ≫
    (Functor.associator w G P').inv ≫ Functor.whiskerRight δ P' ≫
      (Functor.associator F w' P').hom

/-- The component of `foldZero` at `X` is `θ` at `w(X)` followed by `P'` applied to `δ` at `X`. -/
theorem foldZero_app (X : A) :
    (foldZero (w := w) (w' := w') (P := P) (P' := P') (F := F) (G := G) δ θ).app X =
      θ.app (w.obj X) ≫ P'.map (δ.app X) := by
  simp [foldZero]

variable (Rw : DerivedCategory A ⥤ DerivedCategory C)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  (Rw' : DerivedCategory A' ⥤ DerivedCategory C')
  (α' : w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw')
  (Ψ : Rw ⋙ G.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ Rw')

variable [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [Rw'.IsRightDerivedFunctor α' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresA' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The derived fold-in.**  From the derived 2-square `θ.mapDerivedCategory` of the base change
and a comparison `Ψ : Rw ⋙ G.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ Rw'` of the inner
derived functors, the comparison

`(Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory ⟶
  F.mapDerivedCategory ⋙ (Rw' ⋙ P'.mapDerivedCategory)`

for the composites.  Same recipe as `foldZero`, one level up. -/
def foldDerived :
    (Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ (Rw' ⋙ P'.mapDerivedCategory) :=
  (Functor.associator Rw P.mapDerivedCategory F.mapDerivedCategory).hom ≫
    Functor.whiskerLeft Rw θ.mapDerivedCategory.natTrans ≫
      (Functor.associator Rw G.mapDerivedCategory P'.mapDerivedCategory).inv ≫
        Functor.whiskerRight Ψ P'.mapDerivedCategory ≫
          (Functor.associator F.mapDerivedCategory Rw' P'.mapDerivedCategory).hom

/-- The component of `foldDerived` at `K` is `θ.mapDerivedCategory` at `Rw(K)` followed by
`P'.mapDerivedCategory` applied to `Ψ` at `K`. -/
theorem foldDerived_app (K : DerivedCategory A) :
    (foldDerived (P := P) (P' := P') (F := F) (G := G) θ Rw Rw' Ψ).app K =
      θ.mapDerivedCategory.app (Rw.obj K) ≫ P'.mapDerivedCategory.map (Ψ.app K) := by
  simp [foldDerived]

/-- **The degree-zero fold-in, read on the homotopy category, splits.**  Applying
`CategoryTheory.NatTrans.mapHomotopyCategory` to `foldZero` gives the degreewise base change at
`w(K)` followed by `P'` applied to the degreewise `δ`.  Proved on a cochain complex, where it is
`foldZero_app` in each degree, and then transported along the quotient. -/
theorem foldZero_mapHomotopyCategory_app
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory (foldZero (w := w) (w' := w') (P := P) (P' := P') (F := F)
          (G := G) δ θ) (ComplexShape.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory θ.natTrans (ComplexShape.up ℤ)).app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (P'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ)).app K) := by
  obtain ⟨L, rfl⟩ : ∃ L, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L = K :=
    ⟨K.as, rfl⟩
  have hc : (NatTrans.mapHomologicalComplex (foldZero (w := w) (w' := w') (P := P) (P' := P')
          (F := F) (G := G) δ θ) (ComplexShape.up ℤ)).app L =
      (NatTrans.mapHomologicalComplex θ.natTrans (ComplexShape.up ℤ)).app
          ((w.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (P'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex δ (ComplexShape.up ℤ)).app L) := by
    ext i
    exact foldZero_app (w := w) (w' := w') (P := P) (P' := P') (F := F) (G := G) δ θ (L.X i)
  show (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (foldZero (w := w) (w' := w') (P := P) (P' := P')
          (F := F) (G := G) δ θ) (ComplexShape.up ℤ)).app L) =
      (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ.natTrans (ComplexShape.up ℤ)).app
            ((w.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≫
        (P'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient C' (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex δ (ComplexShape.up ℤ)).app L))
  rw [hc, Functor.map_comp]
  rfl

/-- The chase behind `foldDerived_fac`.  Stated at an arbitrary category with the objects
implicit and the morphisms explicit, so that it applies by `exact` across the definitionally
equal spellings of the homotopy-category functor of a composite. -/
private theorem fold_chase {D : Type*} [Category* D]
    {x0 x1 x2 x3 p0 p2 p3 q0 r1 r2 ss z : D}
    (a1 : x0 ⟶ x1) (a2 : x1 ⟶ x2) (a3 : x2 ⟶ x3) (a23 : x1 ⟶ x3) (t : x3 ⟶ p0) (u : p0 ⟶ z)
    (b1 : x2 ⟶ x1) (b2 : x1 ⟶ x0) (b3 : x0 ⟶ p2) (b4 : p2 ⟶ p3) (b5 : p3 ⟶ q0)
    (t0 : x2 ⟶ q0) (gm : q0 ⟶ p0)
    (m1 : p3 ⟶ r1) (m2 : r1 ⟶ r2) (m3 : r2 ⟶ z) (n1 : p2 ⟶ ss) (n2 : ss ⟶ r1) (fz : x0 ⟶ ss)
    (h12 : a1 ≫ b2 = CategoryStruct.id x0) (h21 : a2 ≫ b1 = CategoryStruct.id x1)
    (hb : a3 ≫ t = t0 ≫ gm) (hc : t0 = b1 ≫ b2 ≫ b3 ≫ b4 ≫ b5)
    (ha : b5 ≫ gm ≫ u = m1 ≫ m2 ≫ m3) (he : b4 ≫ m1 = n1 ≫ n2) (hd : b3 ≫ n1 = fz)
    (h23 : a23 = a2 ≫ a3) :
    (a1 ≫ a23) ≫ t ≫ u = fz ≫ (n2 ≫ m2) ≫ m3 := by
  subst h23
  simp only [Category.assoc, reassoc_of% hb, hc, reassoc_of% h21, reassoc_of% h12,
    Category.id_comp, ha, reassoc_of% he, reassoc_of% hd]

/-- Three composable morphisms carried by a functor, with the bracketing the chase needs.
Stated at arbitrary categories with the objects implicit and the morphisms explicit. -/
private theorem map_three {E D : Type*} [Category* E] [Category* D] (Φ : E ⥤ D)
    {a b c d b' c' : E} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (f' : a ⟶ b') (g' : b' ⟶ c') (h' : c' ⟶ d) (hh : (f ≫ g) ≫ h = f' ≫ g' ≫ h') :
    Φ.map f ≫ Φ.map g ≫ Φ.map h = Φ.map f' ≫ Φ.map g' ≫ Φ.map h' := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg Φ.map hh

/-- Two composable morphisms carried by a functor, against a named composite.  Stated at
arbitrary categories with the objects implicit and the morphisms explicit. -/
private theorem map_comp_eq {E D : Type*} [Category* E] [Category* D] (Φ : E ⥤ D)
    {a b c : E} (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ c) (hk : k = f ≫ g) :
    Φ.map f ≫ Φ.map g = Φ.map k := by rw [hk, Φ.map_comp]

include hresA hresA' in
/-- **The factorization transports to the fold-in.**  If `Ψ` factors the unit of
`Rw ⋙ G.mapDerivedCategory` through the degreewise `δ` and the unit of
`F.mapDerivedCategory ⋙ Rw'` — which is what the universal property of right derivation gives —
then `foldDerived` factors the unit of `(Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory`
through `foldZero` and the unit of `F.mapDerivedCategory ⋙ Rw' ⋙ P'.mapDerivedCategory`.

The proof is five facts pasted: the naturality of the derived 2-square at the unit `α`, the
derived 2-square read on the image of `DerivedCategory.Qh`
(`CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh`), the hypothesis `hΨ`, the naturality of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` for `P'` at the degreewise `δ`, and the
splitting `foldZero_mapHomotopyCategory_app`. -/
theorem foldDerived_fac
    (hΨ : postcomposeUnit w G Rw α ≫ Functor.whiskerLeft DerivedCategory.Qh Ψ =
      mapHomotopyCategoryCompQhNatTrans (w ⋙ G) (F ⋙ w') δ ≫ precomposeUnit F w' Rw' α') :
    postcomposeUnit (w ⋙ P) F (Rw ⋙ P.mapDerivedCategory) (postcomposeUnit w P Rw α) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (foldDerived (P := P) (P' := P') (F := F) (G := G) θ Rw Rw' Ψ) =
      mapHomotopyCategoryCompQhNatTrans ((w ⋙ P) ⋙ F) (F ⋙ (w' ⋙ P'))
          (foldZero (w := w) (w' := w') (P := P) (P' := P') (F := F) (G := G) δ θ) ≫
        precomposeUnit F (w' ⋙ P') (Rw' ⋙ P'.mapDerivedCategory)
          (postcomposeUnit w' P' Rw' α') := by
  let := isRightDerivedFunctor_postcompose w P Rw α hresA
  let := isRightDerivedFunctor_postcompose w' P' Rw' α' hresA'
  refine NatTrans.ext (funext fun K => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, postcomposeUnit_app, postcomposeUnit_app,
    precomposeUnit_app, postcomposeUnit_app, Functor.whiskerLeft_app, foldDerived_app,
    mapHomotopyCategoryCompQhNatTrans_app]
  have ha : (G.mapDerivedCategoryFactorsh.inv.app
            ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map (α.app K)) ≫ Ψ.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ)).app K) ≫
        α'.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          Rw'.map (F.mapDerivedCategoryFactorsh.inv.app K) := by
    have h := NatTrans.congr_app hΨ K
    rwa [NatTrans.comp_app, NatTrans.comp_app, postcomposeUnit_app,
      precomposeUnit_app, mapHomotopyCategoryCompQhNatTrans_app,
      Functor.whiskerLeft_app] at h
  have hb := θ.mapDerivedCategory.natTrans.naturality (α.app K)
  have hc := CategoryTheory.TwoSquare.mapDerivedCategory_app_Qh P G F P' θ
    ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hd := foldZero_mapHomotopyCategory_app (w := w) (w' := w') (P := P) (P' := P')
    (F := F) (G := G) δ θ K
  have he := P'.mapDerivedCategoryFactorsh.inv.naturality
    ((NatTrans.mapHomotopyCategory δ (ComplexShape.up ℤ)).app K)
  have ha' := map_three P'.mapDerivedCategory _ _ _ _ _ _ ha
  have hd' := map_comp_eq DerivedCategory.Qh _ _ _ hd
  have h21 : F.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.inv.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        F.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.hom.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
      CategoryStruct.id _ := by
    rw [← F.mapDerivedCategory.map_comp, P.mapDerivedCategoryFactorsh.inv_hom_id_app,
      F.mapDerivedCategory.map_id]
  exact fold_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (F.mapDerivedCategoryFactorsh.inv_hom_id_app _) h21 hb hc ha' he.symm hd'
    (F.mapDerivedCategory.map_comp _ _)

include hresA hresA' in
/-- **The fold-in is the only comparison with that factorization.**  Both
`(Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory` and
`F.mapDerivedCategory ⋙ Rw' ⋙ P'.mapDerivedCategory` are right derived functors of
`(w ⋙ P) ⋙ F` and of `F ⋙ (w' ⋙ P')`, so `CategoryTheory.Functor.rightDerived_ext` makes the
factorization through the unit determine the comparison: anything factoring it the way
`foldDerived_fac` does **is** `foldDerived`. -/
theorem eq_foldDerived
    (Θ : (Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ (Rw' ⋙ P'.mapDerivedCategory))
    (hΘ : postcomposeUnit (w ⋙ P) F (Rw ⋙ P.mapDerivedCategory) (postcomposeUnit w P Rw α) ≫
        Functor.whiskerLeft DerivedCategory.Qh Θ =
      mapHomotopyCategoryCompQhNatTrans ((w ⋙ P) ⋙ F) (F ⋙ (w' ⋙ P'))
          (foldZero (w := w) (w' := w') (P := P) (P' := P') (F := F) (G := G) δ θ) ≫
        precomposeUnit F (w' ⋙ P') (Rw' ⋙ P'.mapDerivedCategory)
          (postcomposeUnit w' P' Rw' α'))
    (hΨ : postcomposeUnit w G Rw α ≫ Functor.whiskerLeft DerivedCategory.Qh Ψ =
      mapHomotopyCategoryCompQhNatTrans (w ⋙ G) (F ⋙ w') δ ≫ precomposeUnit F w' Rw' α') :
    Θ = foldDerived (P := P) (P' := P') (F := F) (G := G) θ Rw Rw' Ψ := by
  let := isRightDerivedFunctor_postcompose w P Rw α hresA
  let := isRightDerivedFunctor_postcompose (w ⋙ P) F (Rw ⋙ P.mapDerivedCategory)
    (postcomposeUnit w P Rw α) hresA
  refine Functor.rightDerived_ext ((Rw ⋙ P.mapDerivedCategory) ⋙ F.mapDerivedCategory)
    (postcomposeUnit (w ⋙ P) F (Rw ⋙ P.mapDerivedCategory) (postcomposeUnit w P Rw α))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  rw [hΘ, foldDerived_fac (w := w) (w' := w') (P := P) (P' := P') (F := F) (G := G) δ θ Rw α
    Rw' α' Ψ hresA hresA' hΨ]

end Stacks.DerivedFunctor

end

