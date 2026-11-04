module

public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Basic
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexAugmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.InjectiveRestrictionAlongAMono
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# The Mayer–Vietoris sequence for the functors `j_{V,*} j_V^{-1}`

Let `C` be a site with binary products, `R` a sheaf of rings on it, and let

```
X₁ --f₁₂--> X₂
|           |
f₁₃         f₂₄
v           v
X₃ --f₃₄--> X₄
```

be a pullback square in `C` whose two arrows into `X₄` are monomorphisms which together cover
`X₄`.  For every sheaf of `R`-modules `F` the restriction maps of
`Stacks.CechSite.SheafLevel.directImage`, the functor `j_{V,*} j_V^{-1}` whose sections over `W`
are `F(V ⨯ W)`, form a complex

`0 ⟶ j_{X₄,*} F ⟶ j_{X₂,*} F ⊞ j_{X₃,*} F ⟶ j_{X₁,*} F ⟶ 0`,

and this complex is **short exact at every injective `F`**: over `W` it is the Mayer–Vietoris
sequence of the sheaf `F` for the square `X_i ⨯ W`, which is again a pullback square with mono
arrows covering `X₄ ⨯ W`, so it is left exact by the sheaf condition; and it is exact on the right
because the restriction of an injective sheaf of modules along a monomorphism of the site is
surjective (`Stacks.Injectives.surjective_presheaf_map_of_injective`, [Stacks, Tag 093X]).

Consequently, for any additive functor `π` out of the sheaves of `R`-modules, the right derived
functors of the three composites `j_{X_i,*} ⋙ π` sit in a long exact sequence
(`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`), and a weak Serre class
containing the derived functors at `X₁`, `X₂` and `X₃` contains those at `X₄`
(`prop_rightDerived_directImage_comp_of_isPullback`).  This is the form of the relative
Mayer–Vietoris sequence of [Stacks, Tag 01EC] that the étale clause of [Stacks, Tag 071N] uses,
on a site rather than a ringed space, and with the open cover replaced by any covering pair of
monomorphisms.

## Main results

* `Stacks.CechSite.SheafLevel.shortExact_of_sections`: a short complex of sheaves of modules
  which is short exact on sections over every object is short exact.
* `Stacks.CechSite.SheafLevel.shortExact_mayerVietorisShortComplex_of_injective`: the
  Mayer–Vietoris complex of the functors `j_{V,*} j_V^{-1}` is short exact at an injective sheaf
  of modules.
* `Stacks.CechSite.SheafLevel.prop_rightDerived_directImage_comp_of_isPullback`: the weak Serre
  transfer through the resulting long exact sequence.

## References

* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u u'

namespace Stacks.CechSite.SheafLevel

variable {C : Type u'} [Category.{u} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

/-! ### Short exactness from sections -/

section Sections

omit [HasBinaryProducts C] [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A short complex of sheaves of modules which is short exact on sections over every object is
short exact.** -/
theorem shortExact_of_sections (S : ShortComplex (SheafOfModules.{u} R))
    (hf : ∀ V : C, Function.Injective (S.f.val.app (op V)))
    (hfg : ∀ ⦃V : C⦄ (z : ToType (S.X₂.val.obj (op V))), S.g.val.app (op V) z = 0 →
      ∃ x : ToType (S.X₁.val.obj (op V)), S.f.val.app (op V) x = z)
    (hg : ∀ V : C, Function.Surjective (S.g.val.app (op V))) :
    S.ShortExact where
  exact := Stacks.SheafOfModules.ComplexLocality.exact_of_locallyExact S fun V z hz ↦
    ⟨⊤, J.top_mem V, fun W p _ ↦ by
      obtain ⟨x, hx⟩ := hfg (V := W)
        (show ToType (S.X₂.val.obj (op W)) from S.X₂.val.map p.op z) (by
          rw [PresheafOfModules.naturality_apply S.g.val p.op z, hz]
          exact map_zero _)
      exact ⟨x, hx⟩⟩
  mono_f := by
    have : Mono S.f.val := PresheafOfModules.mono_of_injective (f := S.f.val)
      (fun {X} ↦ hf X.unop)
    exact (SheafOfModules.forget R).mono_of_mono_map this
  epi_g := Stacks.SheafOfModules.ComplexLocality.epi_of_isLocallySurjective S.g
    ⟨fun {V} y ↦ by
      obtain ⟨x, rfl⟩ := hg V y
      exact J.superset_covering (fun W p _ ↦ ⟨S.X₂.val.map p.op x,
        (PresheafOfModules.naturality_apply S.g.val p.op x)⟩) (J.top_mem V)⟩

end Sections

/-! ### The Mayer–Vietoris complex -/

/-- The transition maps of `Stacks.CechSite.SheafLevel.restriction`, as a natural transformation
`j_{V,*} j_V^{-1} ⟶ j_{W,*} j_W^{-1}` for a morphism `f : W ⟶ V`. -/
def restrictionNatTrans {V W : C} (f : W ⟶ V) : directImage R V ⟶ directImage R W where
  app F := restriction R F f
  naturality _ _ φ := (restriction_naturality R φ f).symm

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The component of `restrictionNatTrans R f` at a sheaf of modules `F` is
`restriction R F f`. -/
@[simp]
theorem restrictionNatTrans_app {V W : C} (f : W ⟶ V) (F : SheafOfModules.{u} R) :
    (restrictionNatTrans R f).app F = restriction R F f := rfl

variable (sq : Square C)

/-- **The Mayer–Vietoris complex of a sheaf of modules for a square of the site**, built from the
functors `j_{V,*} j_V^{-1}`. -/
def mayerVietorisShortComplex (F : SheafOfModules.{u} R) : ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk
    (biprod.lift (restriction R F sq.f₂₄) (restriction R F sq.f₃₄))
    (biprod.desc (restriction R F sq.f₁₂) (-restriction R F sq.f₁₃))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← restriction_comp, ← restriction_comp,
        sq.fac, add_neg_cancel])

/-! ### The square multiplied by an object -/

/-- The square `X_i ⨯ W` obtained by multiplying `sq` with an object `W`. -/
@[simps]
def prodSquare (W : C) : Square C where
  X₁ := sq.X₁ ⨯ W
  X₂ := sq.X₂ ⨯ W
  X₃ := sq.X₃ ⨯ W
  X₄ := sq.X₄ ⨯ W
  f₁₂ := prod.map sq.f₁₂ (𝟙 W)
  f₁₃ := prod.map sq.f₁₃ (𝟙 W)
  f₂₄ := prod.map sq.f₂₄ (𝟙 W)
  f₃₄ := prod.map sq.f₃₄ (𝟙 W)
  fac := by rw [prod.map_map, prod.map_map, sq.fac]

/-- A morphism `g` into `Y ⨯ W` whose first component factors through `f : X ⟶ Y` is the
composite of `prod.lift a (g ≫ prod.snd)` with `prod.map f (𝟙 W)`. -/
private theorem prod_lift_comp_prod_map {X Y W T : C} (f : X ⟶ Y) (g : T ⟶ Y ⨯ W) (a : T ⟶ X)
    (ha : a ≫ f = g ≫ prod.fst) : prod.lift a (g ≫ prod.snd) ≫ prod.map f (𝟙 W) = g := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, ← Category.assoc, prod.lift_fst]
    exact ha
  · rw [Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd]

variable {sq} in
/-- Multiplying a pullback square by an object gives a pullback square. -/
theorem isPullback_prodSquare (h : sq.IsPullback) (W : C) : (prodSquare sq W).IsPullback := by
  have h' : IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ := h
  have hc : ∀ s : PullbackCone (prod.map sq.f₂₄ (𝟙 W)) (prod.map sq.f₃₄ (𝟙 W)),
      (s.fst ≫ prod.fst) ≫ sq.f₂₄ = (s.snd ≫ prod.fst) ≫ sq.f₃₄ := fun s ↦ by
    simpa only [Category.assoc, prod.map_fst] using s.condition =≫ prod.fst
  have hs : ∀ s : PullbackCone (prod.map sq.f₂₄ (𝟙 W)) (prod.map sq.f₃₄ (𝟙 W)),
      s.fst ≫ prod.snd = s.snd ≫ prod.snd := fun s ↦ by
    simpa only [Category.assoc, prod.map_snd, Category.comp_id] using s.condition =≫ prod.snd
  refine Square.IsPullback.mk _ (PullbackCone.IsLimit.mk _
    (fun s ↦ prod.lift (h'.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (hc s)) (s.fst ≫ prod.snd))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · exact prod_lift_comp_prod_map sq.f₁₂ s.fst _ (h'.lift_fst _ _ _)
  · exact (congrArg (prod.lift _ · ≫ _) (hs s)).trans
      (prod_lift_comp_prod_map sq.f₁₃ s.snd _ (h'.lift_snd _ _ _))
  · let m' : s.pt ⟶ sq.X₁ ⨯ W := m
    have h₁' : m' ≫ prod.map sq.f₁₂ (𝟙 W) = s.fst := h₁
    have h₂' : m' ≫ prod.map sq.f₁₃ (𝟙 W) = s.snd := h₂
    have e : ∀ {X Y : C} (f : X ⟶ Y) (m : s.pt ⟶ X ⨯ W) (g : s.pt ⟶ Y ⨯ W),
        m ≫ prod.map f (𝟙 W) = g → (m ≫ prod.fst) ≫ f = g ≫ prod.fst :=
      fun f m g hg ↦ by simp [← hg]
    change m' = _
    refine prod.hom_ext ?_ ?_
    · rw [prod.lift_fst]
      exact h'.hom_ext ((e _ _ _ h₁').trans (h'.lift_fst _ _ _).symm)
        ((e _ _ _ h₂').trans (h'.lift_snd _ _ _).symm)
    · rw [prod.lift_snd]
      exact (by simp : m' ≫ prod.snd = (m' ≫ prod.map sq.f₁₂ (𝟙 W)) ≫ prod.snd).trans
        (congrArg (· ≫ prod.snd) h₁')

/-- A morphism into `Y ⨯ W` whose first component factors through `f : X ⟶ Y` factors through
`prod.map f (𝟙 W)`. -/
theorem eq_prodLift_comp_prodMap {X Y W T : C} (f : X ⟶ Y) (g : T ⟶ Y ⨯ W) (a : T ⟶ X)
    (ha : g ≫ prod.fst = a ≫ f) : g = prod.lift a (g ≫ prod.snd) ≫ prod.map f (𝟙 W) :=
  (prod_lift_comp_prod_map f g a ha.symm).symm

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
variable {sq} in
/-- Multiplying a covering pair of morphisms by an object gives a covering pair. -/
theorem ofTwoArrows_prodSquare_mem (hcov : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄) (W : C) :
    Sieve.ofTwoArrows (prod.map sq.f₂₄ (𝟙 W)) (prod.map sq.f₃₄ (𝟙 W)) ∈ J (sq.X₄ ⨯ W) := by
  refine J.superset_covering (fun T g hg ↦ ?_) (J.pullback_stable (prod.fst : sq.X₄ ⨯ W ⟶ _) hcov)
  obtain ⟨k, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  rw [Sieve.mem_ofArrows_iff]
  cases k
  · exact ⟨.left, prod.lift a (g ≫ prod.snd), eq_prodLift_comp_prodMap sq.f₂₄ g a ha⟩
  · exact ⟨.right, prod.lift a (g ≫ prod.snd), eq_prodLift_comp_prodMap sq.f₃₄ g a ha⟩

/-! ### Short exactness at an injective -/

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The sections of a transition map, with the morphism of products spelled `prod.map`. -/
theorem restriction_val_app (F : SheafOfModules.{u} R) {V V' : C} (f : V' ⟶ V) (W : C)
    (x : ToType (((directImage R V).obj F).val.obj (op W))) :
    (restriction R F f).val.app (op W) x = F.val.presheaf.map (prod.map f (𝟙 W)).op x :=
  (restriction_apply R F f (op W) x).trans
    (congrArg (fun h : V' ⨯ W ⟶ V ⨯ W ↦
      (ConcreteCategory.hom (F.val.presheaf.map h.op)) x) (prod.functor_map_app f W))

section Biprod

variable {M N : SheafOfModules.{u} R} (W : C)

omit [HasBinaryProducts C] [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- A section of a biproduct of sheaves of modules is the sum of its two components. -/
theorem biprod_val_app_eq (z : ToType ((M ⊞ N).val.obj (op W))) :
    z = (biprod.inl : M ⟶ M ⊞ N).val.app (op W) ((biprod.fst : M ⊞ N ⟶ M).val.app (op W) z) +
      (biprod.inr : N ⟶ M ⊞ N).val.app (op W) ((biprod.snd : M ⊞ N ⟶ N).val.app (op W) z) := by
  have h := congrArg (fun φ : M ⊞ N ⟶ M ⊞ N ↦ φ.val.app (op W) z) (biprod.total (X := M) (Y := N))
  exact h.symm

omit [HasBinaryProducts C] [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- Two sections of a biproduct with the same components are equal. -/
theorem biprod_val_app_ext {z z' : ToType ((M ⊞ N).val.obj (op W))}
    (h₁ : (biprod.fst : M ⊞ N ⟶ M).val.app (op W) z = (biprod.fst : M ⊞ N ⟶ M).val.app (op W) z')
    (h₂ : (biprod.snd : M ⊞ N ⟶ N).val.app (op W) z = (biprod.snd : M ⊞ N ⟶ N).val.app (op W) z') :
    z = z' := by
  rw [biprod_val_app_eq R W z, biprod_val_app_eq R W z', h₁, h₂]

end Biprod

variable [HasWeakSheafify J (Type u)]

variable {sq} in
/-- **The Mayer–Vietoris complex of the functors `j_{V,*} j_V^{-1}` is short exact at an injective
sheaf of modules**, for a pullback square whose two arrows into `X₄` are monomorphisms covering
`X₄`. -/
theorem shortExact_mayerVietorisShortComplex_of_injective [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h : sq.IsPullback) (hcov : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)
    (I : SheafOfModules.{u} R) [Injective I] :
    (mayerVietorisShortComplex R sq I).ShortExact := by
  have : Mono sq.f₁₂ := h.mono_f₁₂
  have : ∀ W : C, Mono (prodSquare sq W).f₂₄ := fun W ↦ inferInstanceAs (Mono (prod.map _ _))
  have : ∀ W : C, Mono (prodSquare sq W).f₃₄ := fun W ↦ inferInstanceAs (Mono (prod.map _ _))
  let P := (sheafCompose J (forget AddCommGrpCat.{u})).obj ((SheafOfModules.toSheaf R).obj I)
  have hsc : ∀ W : C, (GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback (J := J)
      (prodSquare sq W) (isPullback_prodSquare h W)
        (ofTwoArrows_prodSquare_mem hcov W)).SheafCondition P.obj := fun W ↦
    GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf _ P
  let S := mayerVietorisShortComplex R sq I
  have kf₁ : ∀ W (x : ToType (S.X₁.val.obj (op W))),
      (biprod.fst : S.X₂ ⟶ _).val.app (op W) (S.f.val.app (op W) x) =
        I.val.presheaf.map (prod.map sq.f₂₄ (𝟙 W)).op x := fun W x ↦
    (congrArg (fun φ : S.X₁ ⟶ _ ↦ φ.val.app (op W) x) (biprod.lift_fst _ _)).trans
      (restriction_val_app R I sq.f₂₄ W x)
  have kf₂ : ∀ W (x : ToType (S.X₁.val.obj (op W))),
      (biprod.snd : S.X₂ ⟶ _).val.app (op W) (S.f.val.app (op W) x) =
        I.val.presheaf.map (prod.map sq.f₃₄ (𝟙 W)).op x := fun W x ↦
    (congrArg (fun φ : S.X₁ ⟶ _ ↦ φ.val.app (op W) x) (biprod.lift_snd _ _)).trans
      (restriction_val_app R I sq.f₃₄ W x)
  have kg₁ : ∀ W (x : ToType (((directImage R sq.X₂).obj I).val.obj (op W))),
      S.g.val.app (op W) ((biprod.inl : _ ⟶ S.X₂).val.app (op W) x) =
        I.val.presheaf.map (prod.map sq.f₁₂ (𝟙 W)).op x := fun W x ↦
    (congrArg (fun φ : _ ⟶ S.X₃ ↦ φ.val.app (op W) x) (biprod.inl_desc _ _)).trans
      (restriction_val_app R I sq.f₁₂ W x)
  have kg₂ : ∀ W (x : ToType (((directImage R sq.X₃).obj I).val.obj (op W))),
      S.g.val.app (op W) ((biprod.inr : _ ⟶ S.X₂).val.app (op W) x) =
        -I.val.presheaf.map (prod.map sq.f₁₃ (𝟙 W)).op x := fun W x ↦
    (congrArg (fun φ : _ ⟶ S.X₃ ↦ φ.val.app (op W) x) (biprod.inr_desc _ _)).trans
      (congrArg Neg.neg (restriction_val_app R I sq.f₁₃ W x))
  refine shortExact_of_sections R S (fun W x y hxy ↦ ?_) (fun W z hz ↦ ?_) (fun W y ↦ ?_)
  · have h₁ := congrArg ((biprod.fst : S.X₂ ⟶ _).val.app (op W)) hxy
    have h₂ := congrArg ((biprod.snd : S.X₂ ⟶ _).val.app (op W)) hxy
    rw [kf₁, kf₁] at h₁
    rw [kf₂, kf₂] at h₂
    exact (hsc W).ext h₁ h₂
  · set z₂ := (biprod.fst : S.X₂ ⟶ _).val.app (op W) z
    set z₃ := (biprod.snd : S.X₂ ⟶ _).val.app (op W) z
    have e : S.g.val.app (op W) z = S.g.val.app (op W) ((biprod.inl : _ ⟶ S.X₂).val.app (op W) z₂) +
        S.g.val.app (op W) ((biprod.inr : _ ⟶ S.X₂).val.app (op W) z₃) :=
      (congrArg (S.g.val.app (op W)) (biprod_val_app_eq R W z)).trans (map_add _ _ _)
    rw [kg₁, kg₂, hz] at e
    have hz' := add_neg_eq_zero.1 e.symm
    refine ⟨(hsc W).glue z₂ z₃ hz', biprod_val_app_ext R W ?_ ?_⟩
    · exact (kf₁ W _).trans ((hsc W).map_f₂₄_op_glue z₂ z₃ hz')
    · exact (kf₂ W _).trans ((hsc W).map_f₃₄_op_glue z₂ z₃ hz')
  · obtain ⟨y₂, hy₂⟩ := Stacks.Injectives.surjective_presheaf_map_of_injective
      (prod.map sq.f₁₂ (𝟙 W)) I y
    exact ⟨(biprod.inl : _ ⟶ S.X₂).val.app (op W) y₂, (kg₁ W y₂).trans hy₂⟩

/-! ### At a terminal object -/

section Terminal

variable {T : C} (hT : IsTerminal T)

omit [J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasWeakSheafify J (Type u)] in
include hT in
/-- At a terminal object the augmentation `F ⟶ j_{T,*} j_T^{-1} F` is an isomorphism: over `Y` it
is `F` applied to the second projection `T ⨯ Y ⟶ Y`, which is an isomorphism. -/
theorem isIso_augmentationAt (F : SheafOfModules.{u} R) : IsIso (augmentationAt R F T) := by
  have hsnd : ∀ Y : C, IsIso (prod.snd : T ⨯ Y ⟶ Y) := fun Y ↦
    ⟨prod.lift (hT.from Y) (𝟙 Y), prod.hom_ext (hT.hom_ext _ _) (by simp), by simp⟩
  have hbij : ∀ Y : Cᵒᵖ, Function.Bijective ((augmentationAt R F T).val.app Y) := fun Y ↦ by
    have : IsIso (F.val.presheaf.map (prod.snd : T ⨯ Y.unop ⟶ Y.unop).op) := by
      have := hsnd Y.unop
      infer_instance
    have hb := (ConcreteCategory.bijective_of_isIso
      (F.val.presheaf.map (prod.snd : T ⨯ Y.unop ⟶ Y.unop).op))
    refine ⟨fun x y hxy ↦ hb.1 ?_, fun z ↦ ?_⟩
    · rwa [augmentationAt_apply, augmentationAt_apply] at hxy
    · obtain ⟨x, hx⟩ := hb.2 z
      exact ⟨x, (augmentationAt_apply R F T Y x).trans hx⟩
  have : Mono (augmentationAt R F T) :=
    (SheafOfModules.forget R).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (f := (augmentationAt R F T).val) fun {V} ↦ (hbij V).1)
  have : Epi (augmentationAt R F T) :=
    (SheafOfModules.forget R).epi_of_epi_map
      (PresheafOfModules.epi_of_surjective (f := (augmentationAt R F T).val) fun {V} ↦ (hbij V).2)
  exact isIso_of_mono_of_epi _

/-- **At a terminal object, `j_{T,*} j_T^{-1}` is the identity**, by the augmentation. -/
def directImageIsoOfIsTerminal : 𝟭 (SheafOfModules.{u} R) ≅ directImage R T :=
  NatIso.ofComponents (fun F ↦ haveI := isIso_augmentationAt R hT F; asIso (augmentationAt R F T))
    (fun φ ↦ (augmentationAt_naturality R φ T).symm)

end Terminal

/-! ### The long exact sequence and the weak Serre transfer -/

section LongExact

open Stacks.Cohomology.AbsoluteMayerVietoris (evalBiprodIso evalBiprodIso_hom_lift
  evalBiprodIso_inv_desc)

/-- `j_{V,*} j_V^{-1}` is additive: on sections over `W` it is the identity of `F(V ⨯ W)`. -/
instance additive_directImage (V : C) : (directImage R V).Additive where
  map_add := rfl

variable {D' : Type*} [Category D'] [Abelian D'] (π : SheafOfModules.{u} R ⥤ D') [π.Additive]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The composite `j_{V,*} j_V^{-1} ⋙ π`. -/
abbrev directImageComp (V : C) : SheafOfModules.{u} R ⥤ D' := directImage R V ⋙ π

/-- The first map of the Mayer–Vietoris sequence of functors. -/
def mayerVietorisι :
    directImageComp R π sq.X₄ ⟶ directImageComp R π sq.X₂ ⊞ directImageComp R π sq.X₃ :=
  biprod.lift (Functor.whiskerRight (restrictionNatTrans R sq.f₂₄) π)
    (Functor.whiskerRight (restrictionNatTrans R sq.f₃₄) π)

/-- The second map of the Mayer–Vietoris sequence of functors. -/
def mayerVietorisπ :
    directImageComp R π sq.X₂ ⊞ directImageComp R π sq.X₃ ⟶ directImageComp R π sq.X₁ :=
  biprod.desc (Functor.whiskerRight (restrictionNatTrans R sq.f₁₂) π)
    (-Functor.whiskerRight (restrictionNatTrans R sq.f₁₃) π)

/-- The two maps of the Mayer–Vietoris sequence of functors, at a sheaf of modules, are `π` of
the Mayer–Vietoris complex. -/
def mayerVietorisAppIso (hiq : mayerVietorisι R sq π ≫ mayerVietorisπ R sq π = 0)
    (F : SheafOfModules.{u} R) :
    NatTrans.appShortComplex (mayerVietorisι R sq π) (mayerVietorisπ R sq π) hiq F ≅
      (mayerVietorisShortComplex R sq F).map π :=
  ShortComplex.isoMk (Iso.refl _)
    (evalBiprodIso (directImageComp R π sq.X₂) (directImageComp R π sq.X₃) F ≪≫
      (π.mapBiprod ((directImage R sq.X₂).obj F) ((directImage R sq.X₃).obj F)).symm)
    (Iso.refl _)
    (by
      dsimp [NatTrans.appShortComplex, mayerVietorisShortComplex]
      rw [Category.id_comp, ← Category.assoc, mayerVietorisι, evalBiprodIso_hom_lift]
      exact (biprod.lift_mapBiprod π ((directImage R sq.X₂).obj F) ((directImage R sq.X₃).obj F)
        (restriction R F sq.f₂₄) (restriction R F sq.f₃₄)).symm)
    (by
      dsimp [NatTrans.appShortComplex, mayerVietorisShortComplex]
      rw [Category.comp_id, Category.assoc, biprod.mapBiprod_inv_map_desc, π.map_neg,
        mayerVietorisπ]
      exact ((Iso.inv_comp_eq _).1 (evalBiprodIso_inv_desc
        (Functor.whiskerRight (restrictionNatTrans R sq.f₁₂) π)
        (-Functor.whiskerRight (restrictionNatTrans R sq.f₁₃) π) F)).symm)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasWeakSheafify J (Type u)] [π.Additive] in
/-- The composite of the two maps `mayerVietorisι` and `mayerVietorisπ` of the Mayer–Vietoris
sequence of functors is zero. -/
theorem mayerVietorisι_comp_mayerVietorisπ :
    mayerVietorisι R sq π ≫ mayerVietorisπ R sq π = 0 := by
  rw [mayerVietorisι, mayerVietorisπ, biprod.lift_desc, Preadditive.comp_neg,
    ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, add_neg_eq_zero]
  refine congrArg (fun α ↦ Functor.whiskerRight α π) (NatTrans.ext (funext fun F ↦ ?_))
  simp only [NatTrans.comp_app, restrictionNatTrans_app, ← restriction_comp, sq.fac]

variable [HasWeakSheafify J (Type u)] [HasInjectiveResolutions (SheafOfModules.{u} R)]
  [∀ V : C, (directImage R V).PreservesInjectiveObjects]

variable {sq} in
/-- **The weak Serre transfer through the Mayer–Vietoris sequence.**  For a pullback square
whose two arrows into `X₄` are monomorphisms covering `X₄`, an additive functor `π` out of the
sheaves of modules, and a weak Serre class `P` of the target: if `P` contains every right derived
functor of `j_{V,*} j_V^{-1} ⋙ π` at a sheaf of modules `F` for `V = X₁, X₂, X₃`, then it contains
those for `V = X₄`. -/
theorem prop_rightDerived_directImage_comp_of_isPullback [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h : sq.IsPullback) (hcov : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)
    (P : ObjectProperty D') [P.IsWeakSerreClass] (F : SheafOfModules.{u} R)
    (h₁ : ∀ n, P (((directImageComp R π sq.X₁).rightDerived n).obj F))
    (h₂ : ∀ n, P (((directImageComp R π sq.X₂).rightDerived n).obj F))
    (h₃ : ∀ n, P (((directImageComp R π sq.X₃).rightDerived n).obj F)) (n : ℕ) :
    P (((directImageComp R π sq.X₄).rightDerived n).obj F) := by
  have hiq := mayerVietorisι_comp_mayerVietorisπ R sq π
  have hinj : ∀ I : SheafOfModules.{u} R, Injective I →
      (NatTrans.appShortComplex (mayerVietorisι R sq π) (mayerVietorisπ R sq π) hiq I).ShortExact :=
    fun I hI ↦ by
      have hS := shortExact_mayerVietorisShortComplex_of_injective R h hcov I
      have : Injective (mayerVietorisShortComplex R sq I).X₁ :=
        Functor.injective_obj (directImage R sq.X₄) I
      exact ShortComplex.shortExact_of_iso (mayerVietorisAppIso R sq π hiq I).symm
        ((hS.splittingOfInjective.map π).shortExact)
  obtain ⟨δ, hmono, hex⟩ :=
    longExact_rightDerived_of_shortExact_on_injectives (mayerVietorisι R sq π)
      (mayerVietorisπ R sq π) hiq hinj
  have hG : ∀ m, P (((directImageComp R π sq.X₂ ⊞ directImageComp R π sq.X₃).rightDerived
      m).obj F) := fun m ↦
    P.prop_of_iso ((evalBiprodIso _ _ F).symm ≪≫
      ((Functor.rightDerivedBiprodIso (directImageComp R π sq.X₂)
        (directImageComp R π sq.X₃) m).app F).symm)
      (P.prop_X₂_of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact
        (h₂ m) (h₃ m))
  cases n with
  | zero =>
    have hS : (ShortComplex.mk ((NatTrans.rightDerived (mayerVietorisι R sq π) 0).app F)
        ((NatTrans.rightDerived (mayerVietorisπ R sq π) 0).app F)
        ((hex 0 F).toIsComplex.zero 0)).Exact := (hex 0 F).exact 0
    have := hmono F
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
      ((ShortComplex.exact_and_mono_f_iff_f_is_kernel _).1 ⟨hS, this⟩).some)
      (P.prop_kernel _ (hG 0) (h₁ 0))
  | succ m =>
    exact P.prop_obj₂_of_exact _ (hex m F).δ₀ (hG m) (h₁ m) (hG (m + 1)) (h₁ (m + 1))

end LongExact

end Stacks.CechSite.SheafLevel

end
