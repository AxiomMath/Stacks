module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompProvider
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The comparison of Tag 03EL around a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi which commutes up to a 2-isomorphism
`s : g ∘ f' ≅ f ∘ g'` (Stacks 04IC). Pulling a sheaf of `𝒪_𝒟`-modules back the two ways around
the square gives two functors, identified by an isomorphism

`m : (f')^* g^* ≅ (g')^* f^*`

assembled from the comparisons of Stacks 03D8 along the two composites, the second one read
through `s`. This file proves that the comparison of [Stacks, Tag 03EL],
`h^*(F ⊗ G) ≅ h^*F ⊗ h^*G`, is compatible with `m`: going down and then across, or across and
then down, gives the same comparison `(f')^* g^*(F ⊗ G) ⟶ (g')^* f^* F ⊗ (g')^* f^* G`. The
same is then proved for total tensor complexes of complexes of modules.

The proof is the composition law of Tag 03EL,
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`, applied twice to the composite
`g ∘ f'`: once for the factorization through `f'` and `g`, and once for the factorization
through `g'` and `f`, the comparison of direct images being the one of `s`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.squarePushforwardIso`: the comparison of direct
  images `g'_* ⋙ f_* ≅ (g ∘ f')_*` read off `s`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.squarePullbackIso`: the isomorphism `m`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackTensorIso_squarePullbackIso`: the comparison
  of Tag 03EL is compatible with `m`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackTensorTotalIso_squarePullbackIso`: the same
  for the total tensor complexes of two complexes of modules.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe u

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X}

/-- The comparison of direct images `g'_* ⋙ f_* ≅ (g ∘ f')_*` of a square which commutes up to
the 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`: the direct image of the composite `f ∘ g'` is the
composite of the direct images on the nose, followed by the inverse of `s`. -/
def squarePushforwardIso (s : TwoIso (g.comp f') (f.comp g')) :
    g'.toModulesHom.toToposHom.pushforward ⋙ f.toModulesHom.toToposHom.pushforward ≅
      (g.comp f').toModulesHom.toToposHom.pushforward :=
  toModulesHomPushforwardIso g' f ≪≫ s.e.symm

omit [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The comparison of direct images of the square carries the composite structure map of `g'`
and `f` to the structure map of `g ∘ f'`: this is the compatibility of `s` with the structure
maps. -/
theorem fSharpSetComp_squarePushforwardIso (s : TwoIso (g.comp f') (f.comp g')) :
    fSharpSetComp g'.toModulesHom f.toModulesHom ≫
        (squarePushforwardIso s).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) =
      fSharpSet (g.comp f').toModulesHom := by
  have h3 : (f.comp g').forgetFSharp ≫ s.e.inv.app (X'.forgetRing.obj X'.O) =
      (g.comp f').forgetFSharp := by
    rw [← s.commutes, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ s.e.inv.app _) (fSharpSetComp_toModulesHomPushforwardIso g' f)).trans h3)

variable (s : TwoIso (g.comp f') (f.comp g'))

/-- The comparison `(g ∘ f')^* ≅ g^* ⋙ (f')^*` of Stacks 03D8 for the factorization of the
composite through `f'` and `g`. -/
abbrev squareCompIsoLeft :
    (g.comp f').toModulesHom.pullbackModules ≅
      g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso f'.toModulesHom g.toModulesHom
    (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
    (fSharpSetComp_toModulesHomPushforwardIso f' g)

/-- The comparison `(g ∘ f')^* ≅ f^* ⋙ (g')^*` of Stacks 03D8 for the factorization of the
composite through `g'` and `f`, read through the 2-isomorphism `s`. -/
abbrev squareCompIsoRight :
    (g.comp f').toModulesHom.pullbackModules ≅
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso g'.toModulesHom f.toModulesHom
    (g.comp f').toModulesHom (squarePushforwardIso s) (fSharpSetComp_squarePushforwardIso s)

/-- **The two pullbacks around a 2-commutative square of ringed topoi agree**:
`(f')^* g^* ≅ (g')^* f^*` on sheaves of modules. -/
def squarePullbackIso :
    g.toModulesHom.pullbackModules ⋙ f'.toModulesHom.pullbackModules ≅
      f.toModulesHom.pullbackModules ⋙ g'.toModulesHom.pullbackModules :=
  (squareCompIsoLeft (g := g) (f' := f')).symm ≪≫ squareCompIsoRight s

/-- The algebra behind `pullbackTensorIso_squarePullbackIso`, over an arbitrary bifunctor: two
factorizations of one comparison `δ` through isomorphisms `c₁` and `c₂` give the same comparison
after transport along `c₁⁻¹ ≫ c₂`. Stated over variables so that instantiating it is
substitution. -/
theorem _root_.CategoryTheory.comparison_transport_of_two_factorizations {𝒳 : Type*} [Category 𝒳]
    (B : 𝒳 × 𝒳 ⥤ 𝒳) {P PL PR P₁ P₂ L₁ L₂ R₁ R₂ LM RM : 𝒳}
    (c₁ : P ⟶ PL) (c₂ : P ⟶ PR) [IsIso c₁] (δ : P ⟶ B.obj (P₁, P₂))
    (c₁F : P₁ ⟶ L₁) (c₁G : P₂ ⟶ L₂) (c₂F : P₁ ⟶ R₁) (c₂G : P₂ ⟶ R₂)
    (mF : L₁ ⟶ R₁) (mG : L₂ ⟶ R₂) (m : PL ⟶ PR)
    (l₁ : PL ⟶ LM) (l₂ : LM ⟶ B.obj (L₁, L₂)) (r₁ : PR ⟶ RM) (r₂ : RM ⟶ B.obj (R₁, R₂))
    (hmF : c₁F ≫ mF = c₂F) (hmG : c₁G ≫ mG = c₂G) (hm : c₁ ≫ m = c₂)
    (hL : δ ≫ B.map ((c₁F, c₁G) : ((P₁, P₂) : 𝒳 × 𝒳) ⟶ (L₁, L₂)) = c₁ ≫ l₁ ≫ l₂)
    (hR : δ ≫ B.map ((c₂F, c₂G) : ((P₁, P₂) : 𝒳 × 𝒳) ⟶ (R₁, R₂)) = c₂ ≫ r₁ ≫ r₂) :
    l₁ ≫ l₂ ≫ B.map ((mF, mG) : ((L₁, L₂) : 𝒳 × 𝒳) ⟶ (R₁, R₂)) = m ≫ r₁ ≫ r₂ := by
  rw [← cancel_epi c₁, reassoc_of% hm, ← hR, ← hmF, ← hmG, ← reassoc_of% hL, ← B.map_comp]
  rfl

variable [HasWeakSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of Tag 03EL is compatible with a 2-commutative square of ringed topoi.**
For sheaves of `𝒪_𝒟`-modules `F` and `G`, the comparison along `g` pulled back along `f'`,
followed by the comparison along `f'` and by `m` in each factor, is `m` followed by the
comparison along `f` pulled back along `g'` and by the comparison along `g'`. -/
theorem pullbackTensorIso_squarePullbackIso
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f'.toModulesHom.pullbackModules.map
          ((Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).hom.app (F, G)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f'.toModulesHom).hom.app
          (g.toModulesHom.pullbackModules.obj F, g.toModulesHom.pullbackModules.obj G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)).map
          (((squarePullbackIso s).hom.app F, (squarePullbackIso s).hom.app G) :
            ((f'.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj F),
                f'.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj G)) :
              SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) ×
                SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⟶
            (g'.toModulesHom.pullbackModules.obj (f.toModulesHom.pullbackModules.obj F),
              g'.toModulesHom.pullbackModules.obj (f.toModulesHom.pullbackModules.obj G))) =
      (squarePullbackIso s).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj (F, G)) ≫
        g'.toModulesHom.pullbackModules.map
          ((Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (F, G)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso g'.toModulesHom).hom.app
          (f.toModulesHom.pullbackModules.obj F, f.toModulesHom.pullbackModules.obj G) := by
  have hL := Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp f'.toModulesHom
    g.toModulesHom (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
    (fSharpSetComp_toModulesHomPushforwardIso f' g) F G
  have hR := Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp g'.toModulesHom
    f.toModulesHom (g.comp f').toModulesHom (squarePushforwardIso s)
    (fSharpSetComp_squarePushforwardIso s) F G
  let c₁ := squareCompIsoLeft (g := g) (f' := f')
  let c₂ := squareCompIsoRight s
  have hm : ∀ M, c₁.hom.app M ≫ (squarePullbackIso s).hom.app M = c₂.hom.app M := fun M =>
    Iso.hom_inv_id_app_assoc _ _ _
  refine CategoryTheory.comparison_transport_of_two_factorizations
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X'.O))
    (c₁.hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj (F, G)))
    (c₂.hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj (F, G)))
    ((Stacks.SheafOfModules.pullbackTensorIso (g.comp f').toModulesHom).hom.app (F, G))
    (c₁.hom.app F) (c₁.hom.app G) (c₂.hom.app F) (c₂.hom.app G)
    ((squarePullbackIso s).hom.app F) ((squarePullbackIso s).hom.app G)
    ((squarePullbackIso s).hom.app
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj (F, G)))
    _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · exact hm F
  · exact hm G
  · exact hm _
  · convert hL using 1
  · convert hR using 1


/-! ### The total tensor complexes -/

variable [HasSheafify X'.J AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]

open Stacks.Sheaves.DerivedPullback in
/-- The isomorphism `m` of the two pullbacks around the square, applied termwise to a complex:
`(f')^* g^* K ≅ (g')^* f^* K` for a complex `K` of `𝒪_𝒟`-modules. -/
def squarePullbackComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplexFunctor f'.toModulesHom).obj ((pullbackComplexFunctor g.toModulesHom).obj K) ≅
      (pullbackComplexFunctor g'.toModulesHom).obj
        ((pullbackComplexFunctor f.toModulesHom).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (squarePullbackIso s).app (K.X n))
    (fun i j _ => ((squarePullbackIso s).hom.naturality (K.d i j)).symm)

open Stacks.Sheaves.DerivedPullback in
omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- In degree `n`, the termwise isomorphism `m` is `m` applied to the term `K.X n`. -/
@[simp]
theorem squarePullbackComplexIso_hom_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) :
    (squarePullbackComplexIso s K).hom.f n = (squarePullbackIso s).hom.app (K.X n) :=
  rfl

open Stacks.Sheaves.DerivedPullback in
omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] in
/-- The termwise isomorphism `m` is natural in the complex. -/
theorem squarePullbackComplexIso_hom_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : K ⟶ L) :
    (pullbackComplexFunctor f'.toModulesHom).map ((pullbackComplexFunctor g.toModulesHom).map φ) ≫
        (squarePullbackComplexIso s L).hom =
      (squarePullbackComplexIso s K).hom ≫
        (pullbackComplexFunctor g'.toModulesHom).map
          ((pullbackComplexFunctor f.toModulesHom).map φ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  simpa using ((squarePullbackIso s).hom.naturality (φ.f n))

/-- The algebra behind `pullbackTensorTotalIso_squarePullbackIso`, over variables: a summand of a
total complex is carried by the two composites through the module-level compatibility `key`. -/
theorem _root_.CategoryTheory.total_comparison_square_aux {𝒳 : Type*} [Category 𝒳]
    {A₀ A₁ A₂ A₃ A₄ T₁ T₂ S₀ S₁ S₂ S₃ S₄ _S₅ : 𝒳}
    (a : A₀ ⟶ A₁) (u : A₁ ⟶ A₂) (u' : A₂ ⟶ A₁) (t₁ : A₁ ⟶ T₁) (M₁ : T₁ ⟶ T₂) (mm : A₂ ⟶ A₃)
    (t₂ : A₃ ⟶ A₄) (t₃ : A₄ ⟶ T₂) (d₁ : A₀ ⟶ S₁) (i₁ : S₁ ⟶ T₁) (Bm : S₁ ⟶ S₂) (i₂ : S₂ ⟶ T₂)
    (dg : S₀ ⟶ A₀) (dginv : A₀ ⟶ S₀) (gι : S₀ ⟶ A₂) (mP : S₀ ⟶ S₃) (gfι : S₃ ⟶ A₃)
    (gδf : S₃ ⟶ S₄) (gι' : S₄ ⟶ A₄) (δg : S₄ ⟶ S₂)
    (huu : u ≫ u' = 𝟙 A₁) (hdg : dginv ≫ dg = 𝟙 A₀)
    (h₁ : a ≫ t₁ = d₁ ≫ i₁) (h₂ : i₁ ≫ M₁ = Bm ≫ i₂) (h₃ : a ≫ u = dginv ≫ gι)
    (h₄ : gι ≫ mm = mP ≫ gfι) (h₅ : gfι ≫ t₂ = gδf ≫ gι') (h₆ : gι' ≫ t₃ = δg ≫ i₂)
    (key : dg ≫ d₁ ≫ Bm = mP ≫ gδf ≫ δg) :
    a ≫ u ≫ u' ≫ t₁ ≫ M₁ = a ≫ u ≫ mm ≫ t₂ ≫ t₃ := by
  rw [reassoc_of% huu, reassoc_of% h₁, h₂, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅, h₆,
    ← reassoc_of% key, reassoc_of% hdg]

open Stacks.Sheaves.DerivedPullback in
/-- **The comparison of total tensor complexes of Tag 03EL is compatible with a 2-commutative
square of ringed topoi.** For complexes `P` and `N` of `𝒪_𝒟`-modules, the comparison along `g`
pulled back along `f'`, followed by the comparison along `f'` and by `m` in each factor, is `m`
followed by the comparison along `f` pulled back along `g'` and by the comparison along `g'`.

Both sides are morphisms out of `(f')^* g^* Tot(P ⊗ N)`; after the comparison along `g` they are
morphisms out of `(f')^* Tot(g^*P ⊗ g^*N)`, determined by their restrictions to the pullbacks of
the summands, and on a summand this is `pullbackTensorIso_squarePullbackIso`. -/
theorem pullbackTensorTotalIso_squarePullbackIso
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplexFunctor f'.toModulesHom).map (pullbackTensorTotalIso g.toModulesHom P N).hom ≫
        (pullbackTensorTotalIso f'.toModulesHom ((pullbackComplexFunctor g.toModulesHom).obj P)
          ((pullbackComplexFunctor g.toModulesHom).obj N)).hom ≫
        HomologicalComplex.mapBifunctorMap ((squarePullbackComplexIso s P).hom)
          ((squarePullbackComplexIso s N).hom)
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ) =
      (squarePullbackComplexIso s (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))).hom ≫
        (pullbackComplexFunctor g'.toModulesHom).map
          (pullbackTensorTotalIso f.toModulesHom P N).hom ≫
        (pullbackTensorTotalIso g'.toModulesHom ((pullbackComplexFunctor f.toModulesHom).obj P)
          ((pullbackComplexFunctor f.toModulesHom).obj N)).hom := by
  ext n : 1
  rw [← cancel_epi (((pullbackComplexFunctor f'.toModulesHom).map
    (pullbackTensorTotalIso g.toModulesHom P N).inv).f n)]
  refine hom_ext_pullbackTotal f'.toModulesHom ((pullbackComplexFunctor g.toModulesHom).obj P)
    ((pullbackComplexFunctor g.toModulesHom).obj N) n (fun p q hpq => ?_)
  have hg : HomologicalComplex.ιMapBifunctor ((pullbackComplexFunctor g.toModulesHom).obj P)
        ((pullbackComplexFunctor g.toModulesHom).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y'.O) (ComplexShape.up ℤ) p q n hpq ≫
      (pullbackTensorTotalIso g.toModulesHom P N).inv.f n =
        (Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).inv.app (P.X p, N.X q) ≫
          g.toModulesHom.pullbackModules.map (HomologicalComplex.ιMapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq) := by
    rw [← cancel_epi ((Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).hom.app
      (P.X p, N.X q)), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% (ι_pullbackTensorTotalIso_hom g.toModulesHom P N p q n hpq),
      ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    exact Category.comp_id _
  have hf := ι_pullbackTensorTotalIso_hom f.toModulesHom P N p q n hpq
  have hf' := ι_pullbackTensorTotalIso_hom f'.toModulesHom
    ((pullbackComplexFunctor g.toModulesHom).obj P) ((pullbackComplexFunctor g.toModulesHom).obj N)
    p q n hpq
  have hg' := ι_pullbackTensorTotalIso_hom g'.toModulesHom
    ((pullbackComplexFunctor f.toModulesHom).obj P) ((pullbackComplexFunctor f.toModulesHom).obj N)
    p q n hpq
  have hm := (squarePullbackIso s).hom.naturality (HomologicalComplex.ιMapBifunctor P N
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq)
  have key := pullbackTensorIso_squarePullbackIso s (P.X p) (N.X q)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    squarePullbackComplexIso_hom_f]
  have h₃ := congrArg f'.toModulesHom.pullbackModules.map hg
  simp only [Functor.map_comp] at h₃
  have h₅ := congrArg g'.toModulesHom.pullbackModules.map hf
  simp only [Functor.map_comp] at h₅
  have hinv : ∀ {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)}
      (e : A ≅ B), f'.toModulesHom.pullbackModules.map e.inv ≫
        f'.toModulesHom.pullbackModules.map e.hom = 𝟙 _ := fun e => by
    rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
  have huu := hinv
    ((HomologicalComplex.eval _ _ n).mapIso (pullbackTensorTotalIso g.toModulesHom P N))
  have hdg := hinv ((Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).app (P.X p, N.X q))
  have h₂ : HomologicalComplex.ιMapBifunctor
        ((pullbackComplexFunctor f'.toModulesHom).obj
          ((pullbackComplexFunctor g.toModulesHom).obj P))
        ((pullbackComplexFunctor f'.toModulesHom).obj
          ((pullbackComplexFunctor g.toModulesHom).obj N))
        (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ) p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap (squarePullbackComplexIso s P).hom
        (squarePullbackComplexIso s N).hom (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)
        (ComplexShape.up ℤ)).f n =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)).map
          (((squarePullbackIso s).hom.app (P.X p), (squarePullbackIso s).hom.app (N.X q)) :
            ((f'.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj (P.X p)),
                f'.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj (N.X q))) :
              SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O) ×
                SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ⟶
            (g'.toModulesHom.pullbackModules.obj (f.toModulesHom.pullbackModules.obj (P.X p)),
              g'.toModulesHom.pullbackModules.obj (f.toModulesHom.pullbackModules.obj (N.X q)))) ≫
        HomologicalComplex.ιMapBifunctor
          ((pullbackComplexFunctor g'.toModulesHom).obj
            ((pullbackComplexFunctor f.toModulesHom).obj P))
          ((pullbackComplexFunctor g'.toModulesHom).obj
            ((pullbackComplexFunctor f.toModulesHom).obj N))
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ) p q n hpq := by
    refine (HomologicalComplex.ι_mapBifunctorMap (squarePullbackComplexIso s P).hom
      (squarePullbackComplexIso s N).hom (Stacks.SheafOfModules.Tensor.sheafTensor X'.O)
      (ComplexShape.up ℤ) p q n hpq).trans ?_
    simp only [Functor.uncurry_obj_map, Category.assoc, squarePullbackComplexIso_hom_f]
    dsimp only [Functor.mapHomologicalComplex_obj_X]
  dsimp only [Functor.mapHomologicalComplex_obj_X, Functor.uncurry_obj_obj, Functor.comp_obj,
    Functor.prod_obj, Functor.mapIso_inv, Functor.mapIso_hom, HomologicalComplex.eval_map,
    Iso.app_inv, Iso.app_hom] at hf' hg' h₂ h₃ h₅ hm huu hdg key ⊢
  rw [reassoc_of% huu, reassoc_of% hf']
  rw [h₂]
  rw [reassoc_of% h₃]
  rw [reassoc_of% hm]
  rw [reassoc_of% h₅]
  rw [hg']
  rw [← reassoc_of% key]
  rw [reassoc_of% hdg]

end AlgebraicGeometry.RingedToposHom.TwoIso

end
