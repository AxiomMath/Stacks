module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.Cover
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct

/-!
# The groupoid structure on the moduli spaces of a Keel–Mori cover (Stacks 0DUT)

Let `C` be a Keel–Mori cover of an algebraic stack `𝒳`
(`AlgebraicGeometry.Stack.KeelMoriCover`), with moduli spaces `f i : 𝒳 i ⟶ M i` and, for each
pair, the separated étale morphisms `s i j : N i j ⟶ M i`, `t i j : N i j ⟶ M j`. This file
constructs the identity, inverse and composition of the proof of Stacks 0DUT, piece by piece:

* `e i : M i ⟶ N i i` with `e i ≫ s i i = 𝟙` and `e i ≫ t i i = 𝟙`, from the diagonal
  `𝒳 i ⟶ 𝒳 i ×_𝒳 𝒳 i`;
* `inv i j : N i j ⟶ N j i` exchanging `s` and `t`, from the exchange of factors;
* `comp i j k : N i j ×_{t, M j, s} N j k ⟶ N i k` compatible with `s` and `t`, from the
  projection `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ 𝒳 i ×_𝒳 𝒳 k`. Here the moduli space of the triple product is
  `N i j ×_{M j} N j k`, a flat base change of the moduli space of `𝒳 i ×_𝒳 𝒳 j`.

Each is obtained from the universal property of a categorical moduli space.

## Main definitions

* `AlgebraicGeometry.Stack.KeelMoriCover.e`, `.inv`, `.comp`

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.e_comp_s`, `e_comp_t`, `inv_comp_s`, `inv_comp_t`,
  `comp_comp_s`, `comp_comp_t`.
* `CategoryTheory.Bicategory.isTwoFibreProduct_of_isTwoFibreProduct_paste'`: the converse of the
  pasting lemma for categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **The pasting lemma, converse direction (Stacks 003Q), for categories fibred in groupoids.**
If `Q` is a 2-fibre product and the rectangle `Q.paste T` is one, then so is `T`. -/
noncomputable def isTwoFibreProduct_of_isTwoFibreProduct_paste'
    {𝒳 𝒴 𝒵 𝒯 : CatFiberedInGroupoids.{v₁, v₁, u₁, max u₁ v₁} C}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {k : 𝒯 ⟶ 𝒴}
    {Q : TwoCommSq f g} (hQ : IsTwoFibreProduct Q)
    (T : TwoCommSq Q.snd k) (hQT : IsTwoFibreProduct (Q.paste T)) : IsTwoFibreProduct T := by
  let D := CatFiberedInGroupoids.twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} Q.snd k
  have hD : IsTwoFibreProduct D :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} Q.snd k
  let ρ : TwoCommSq.PreHom T D := _root_.Quotient.out (hD.from T)
  have hρ : ρ.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct hQT (isTwoFibreProduct_paste hQ hD)
      (ρ.paste Q)
  exact isTwoFibreProduct_of_isEquivalence_to hD ρ hρ

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Equalities of 1-morphisms into the category attached to a presheaf -/

section Discrete

variable {A A' A'' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Composition of 1-morphisms into the category attached to a presheaf is associative on the
nose. -/
theorem discrete_assoc (x : A ⟶ A') (y : A' ⟶ A'') (z : A'' ⟶ fibredCategory B S hS F) :
    (x ≫ y) ≫ z = x ≫ (y ≫ z) :=
  hom_eq_of_hom₂ B S hS (Bicategory.associator x y z).hom

/-- For a 1-morphism `z` into the category attached to a presheaf, `𝟙 A ≫ z = z`. -/
theorem discrete_id_comp (z : A ⟶ fibredCategory B S hS F) : 𝟙 A ≫ z = z :=
  hom_eq_of_hom₂ B S hS (Bicategory.leftUnitor z).hom

/-- If there is a 2-morphism `x ⟶ y`, then `x ≫ z = y ≫ z` for every 1-morphism `z` into the
category attached to a presheaf. -/
theorem discrete_whisker {x y : A ⟶ A'} (θ : x ⟶ y) (z : A' ⟶ fibredCategory B S hS F) :
    x ≫ z = y ≫ z :=
  hom_eq_of_hom₂ B S hS (Bicategory.whiskerRight θ z)

/-- Equal 1-morphisms `y = z` into the category attached to a presheaf give `x ≫ y = x ≫ z`. -/
theorem discrete_whiskerLeft (x : A ⟶ A') {y z : A' ⟶ fibredCategory B S hS F} (h : y = z) :
    x ≫ y = x ≫ z := by rw [h]

/-- Chasing a 1-morphism through two commuting squares into the category attached to a presheaf:
if `x ≫ m = u ≫ φ` and `φ ≫ s = p ≫ q`, then `x ≫ (m ≫ s) = (u ≫ p) ≫ q`. -/
private theorem discrete_comp_comp_eq {A₁ A₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
    (BigFppfOver B S hS)} {x : A ⟶ A'} {m : A' ⟶ A''} {s : A'' ⟶ fibredCategory B S hS F}
    {u : A ⟶ A₁} {φ : A₁ ⟶ A''} {p : A₁ ⟶ A₂} {q : A₂ ⟶ fibredCategory B S hS F}
    (hm : x ≫ m = u ≫ φ) (hs : φ ≫ s = p ≫ q) : x ≫ (m ≫ s) = (u ≫ p) ≫ q :=
  calc x ≫ (m ≫ s) = (x ≫ m) ≫ s := (discrete_assoc _ _ _).symm
    _ = (u ≫ φ) ≫ s := by rw [hm]
    _ = u ≫ (φ ≫ s) := discrete_assoc _ _ _
    _ = u ≫ (p ≫ q) := discrete_whiskerLeft u hs
    _ = (u ≫ p) ≫ q := (discrete_assoc _ _ _).symm

end Discrete

/-- A categorical moduli space `p` out of `𝒳` factors every 1-morphism `𝒳 ⟶ Y` through a morphism
of schemes `X ⟶ Y`, up to the equality of 1-morphisms. -/
private theorem exists_hom_of_isCategoricalModuliSpace
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {X Y : BigFppfOver B S hS} {p : 𝒳 ⟶ fibredCategory B S hS (yoneda.obj X)}
    (hp : IsCategoricalModuliSpace B S hS ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ p)
    (w : 𝒳 ⟶ fibredCategory B S hS (yoneda.obj Y)) :
    ∃ e : X ⟶ Y, p ≫ (associatedMap B S hS (yoneda.map e)).1 = w := by
  obtain ⟨h, ⟨η⟩, -⟩ := hp ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ w
  exact ⟨Yoneda.fullyFaithful.preimage h.hom, by
    rw [Yoneda.fullyFaithful.map_preimage]
    exact hom_eq_of_hom₂ B S hS η.hom⟩

/-- **A 2-fibre product over the category attached to a presheaf may be read with equal
projections, over equal legs, and with any filler.** -/
noncomputable def isTwoFibreProduct_congr_of_discrete'
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a a' : 𝒴 ⟶ fibredCategory B S hS F} {f f' : 𝒳 ⟶ fibredCategory B S hS F}
    (ha : a = a') (hf : f = f')
    (P : Bicategory.TwoCommSq a f) (hP : Bicategory.IsTwoFibreProduct P)
    {x : P.pt ⟶ 𝒴} {y : P.pt ⟶ 𝒳} (hx : P.fst = x) (hy : P.snd = y)
    (φ : x ≫ a' ≅ y ≫ f') :
    Bicategory.IsTwoFibreProduct (⟨P.pt, x, y, φ⟩ : Bicategory.TwoCommSq a' f') := by
  subst ha hf hx hy
  exact isTwoFibreProduct_of_eq_of_discrete B S hS P hP φ

namespace KeelMoriCover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (C : KeelMoriCover B S hS 𝒳)

/-! ### The identity -/

/-- The diagonal square `(𝒳 i, 𝟙, 𝟙)` over the cospan `(g i, g i)`. -/
noncomputable abbrev diagSq (i : C.ι) : Bicategory.TwoCommSq (C.map i) (C.map i) :=
  ⟨C.obj i, 𝟙 _, 𝟙 _, Iso.refl _⟩

/-- The diagonal `𝒳 i ⟶ 𝒳 i ×_𝒳 𝒳 i`, with its comparisons to the two projections. -/
noncomputable def diag (i : C.ι) : Bicategory.TwoCommSq.PreHom (C.diagSq i) (C.pairSq i i) :=
  Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map i)) _

/-- There is a morphism `e : M i ⟶ N i i` through which the moduli map `f i` composed with `e`
agrees with the diagonal `𝒳 i ⟶ 𝒳 i ×_𝒳 𝒳 i` followed by `φ i i`. -/
theorem exists_e (i : C.ι) :
    ∃ e : C.M i ⟶ C.N i i,
      (C.f i).hom ≫ (associatedMap B S hS (yoneda.map e)).1 =
        (C.diag i).hom.hom ≫ (C.φ i i).hom :=
  exists_hom_of_isCategoricalModuliSpace (C.isCategoricalModuliSpace_f i) _

/-- **The identity `e i : M i ⟶ N i i`.** -/
noncomputable def e (i : C.ι) : C.M i ⟶ C.N i i := (C.exists_e i).choose

/-- The composite of `f i` with `e i` is the diagonal `𝒳 i ⟶ 𝒳 i ×_𝒳 𝒳 i` followed by
`φ i i`. -/
theorem f_comp_e (i : C.ι) :
    (C.f i).hom ≫ (associatedMap B S hS (yoneda.map (C.e i))).1 =
      (C.diag i).hom.hom ≫ (C.φ i i).hom :=
  (C.exists_e i).choose_spec

/-- The 1-morphism attached to the Yoneda image of `a ≫ b` is the composite of those attached to
`a` and to `b`. -/
theorem associatedMap_yoneda_comp {X Y Z : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (associatedMap B S hS (yoneda.map (a ≫ b))).1 =
      (associatedMap B S hS (yoneda.map a)).1 ≫ (associatedMap B S hS (yoneda.map b)).1 := by
  rw [Functor.map_comp, associatedMap_comp]

/-- The 1-morphism attached to the Yoneda image of `𝟙 X` is the identity. -/
theorem associatedMap_yoneda_id (X : BigFppfOver B S hS) :
    (associatedMap B S hS (yoneda.map (𝟙 X))).1 = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_id]
  exact associatedMap_id_eq B S hS _

/-- The identity is a section of the source: `e i ≫ s i i = 𝟙 (M i)`. -/
theorem e_comp_s (i : C.ι) : C.e i ≫ C.s i i = 𝟙 _ := by
  refine C.hom_ext_M _ _ ?_
  rw [associatedMap_yoneda_comp, associatedMap_yoneda_id]
  exact (discrete_comp_comp_eq (C.f_comp_e i) (C.φ_comp_s i i)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.diag i).isoFst).inv _).trans
      ((discrete_id_comp _).trans (hom_eq_of_hom₂ B S hS (Bicategory.rightUnitor _).hom).symm))

/-- The identity is a section of the target: `e i ≫ t i i = 𝟙 (M i)`. -/
theorem e_comp_t (i : C.ι) : C.e i ≫ C.t i i = 𝟙 _ := by
  refine C.hom_ext_M _ _ ?_
  rw [associatedMap_yoneda_comp, associatedMap_yoneda_id]
  exact (discrete_comp_comp_eq (C.f_comp_e i) (C.φ_comp_t i i)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.diag i).isoSnd).inv _).trans
      ((discrete_id_comp _).trans (hom_eq_of_hom₂ B S hS (Bicategory.rightUnitor _).hom).symm))

/-! ### The second morphism of a pair is separated and étale -/

/-- **`t i j` is an isomorphism followed by a separated étale morphism**: there are an
isomorphism `e : N i j ≅ N'` and a separated étale `s' : N' ⟶ M j` with `t i j = e.hom ≫ s'`. -/
theorem exists_t_eq (i j : C.ι) :
    ∃ (N' : BigFppfOver B S hS) (e : C.N i j ≅ N') (s' : N' ⟶ C.M j),
      Etale ((BigFppfOver.toScheme B S hS).map s') ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map s') ∧
      C.t i j = e.hom ≫ s' := by
  obtain ⟨N', φ', s', hcomm, het, hsep, ⟨hP⟩⟩ :=
    exists_moduliSquare_of_isEtale_of_isSeparated B S hS (C.pr₂ i j) (C.wellNighAffine j)
      (C.isEtale_pr₂ i j) (C.isSeparated_pr₂ i j) (C.inducesIsomorphismAt_pr₂ i j) (C.M j)
      (C.f j) (C.isCategoricalModuliSpace_f j)
  let a : (⟨yoneda.obj N', isAlgebraicSpace_yoneda B S hS N'⟩ : AlgebraicSpaces B S hS) ⟶
      C.Msp j := ObjectProperty.homMk (yoneda.map s')
  have ha : Space.IsFlat B S hS a.hom := (isFlat_yoneda_map_iff B S hS s').2 inferInstance
  have hu := isUniformCategoricalModuliSpace_fst B S hS (C.isUniformCategoricalModuliSpace_f j)
    a ha _ hP
  have hφ' : IsCategoricalModuliSpace B S hS
      ⟨yoneda.obj N', isAlgebraicSpace_yoneda B S hS N'⟩ φ'.hom :=
    isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hu
  obtain ⟨e, he⟩ := exists_iso_of_isCategoricalModuliSpace B S hS (C.isCategoricalModuliSpace_φ i j)
    hφ'
  let e' : C.N i j ≅ N' := Yoneda.fullyFaithful.preimageIso ((ObjectProperty.ι _).mapIso e)
  have he' : yoneda.map e'.hom = e.hom.hom := Yoneda.fullyFaithful.map_preimage _
  refine ⟨N', e', s', het, hsep, C.hom_ext_N _ _ ?_⟩
  rw [φ_comp_t, associatedMap_yoneda_comp]
  calc (C.pr₂ i j).hom ≫ (C.f j).hom = φ'.hom ≫ (associatedMap B S hS (yoneda.map s')).1 :=
        hcomm.symm
    _ = ((C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map e'.hom)).1) ≫
          (associatedMap B S hS (yoneda.map s')).1 := by rw [he', he]
    _ = (C.φ i j).hom ≫ ((associatedMap B S hS (yoneda.map e'.hom)).1 ≫
          (associatedMap B S hS (yoneda.map s')).1) := discrete_assoc _ _ _

/-- The morphism `t i j : N i j ⟶ M j` is étale. -/
instance etale_t (i j : C.ι) : Etale ((BigFppfOver.toScheme B S hS).map (C.t i j)) := by
  obtain ⟨N', e, s', het, -, h⟩ := C.exists_t_eq i j
  rw [h, Functor.map_comp]
  infer_instance

/-- The morphism `t i j : N i j ⟶ M j` is separated. -/
instance isSeparated_t (i j : C.ι) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (C.t i j)) := by
  obtain ⟨N', e, s', -, hsep, h⟩ := C.exists_t_eq i j
  rw [h, Functor.map_comp]
  infer_instance

/-! ### The inverse -/

/-- The exchange of factors `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j ×_𝒳 𝒳 i`, with its comparisons. -/
noncomputable def swap (i j : C.ι) :
    Bicategory.TwoCommSq.PreHom (C.pairSq i j).swap (C.pairSq j i) :=
  Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map j) (C.map i)) _

/-- There is a morphism `v : N i j ⟶ N j i` such that `φ i j` composed with `v` agrees with the
exchange of factors `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j ×_𝒳 𝒳 i` followed by `φ j i`. -/
theorem exists_inv (i j : C.ι) :
    ∃ v : C.N i j ⟶ C.N j i,
      (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map v)).1 =
        (C.swap i j).hom.hom ≫ (C.φ j i).hom :=
  exists_hom_of_isCategoricalModuliSpace (C.isCategoricalModuliSpace_φ i j) _

/-- **The inverse `inv i j : N i j ⟶ N j i`.** -/
noncomputable def inv (i j : C.ι) : C.N i j ⟶ C.N j i := (C.exists_inv i j).choose

/-- The composite of `φ i j` with `inv i j` is the exchange of factors
`𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j ×_𝒳 𝒳 i` followed by `φ j i`. -/
theorem φ_comp_inv (i j : C.ι) :
    (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map (C.inv i j))).1 =
      (C.swap i j).hom.hom ≫ (C.φ j i).hom :=
  (C.exists_inv i j).choose_spec

/-- The inverse exchanges source and target: `inv i j ≫ s j i = t i j`. -/
theorem inv_comp_s (i j : C.ι) : C.inv i j ≫ C.s j i = C.t i j := by
  refine C.hom_ext_N _ _ ?_
  rw [associatedMap_yoneda_comp]
  exact (discrete_comp_comp_eq (C.φ_comp_inv i j) (C.φ_comp_s j i)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.swap i j).isoFst).inv _).trans
      (C.φ_comp_t i j).symm)

/-- The inverse exchanges target and source: `inv i j ≫ t j i = s i j`. -/
theorem inv_comp_t (i j : C.ι) : C.inv i j ≫ C.t j i = C.s i j := by
  refine C.hom_ext_N _ _ ?_
  rw [associatedMap_yoneda_comp]
  exact (discrete_comp_comp_eq (C.φ_comp_inv i j) (C.φ_comp_t j i)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.swap i j).isoSnd).inv _).trans
      (C.φ_comp_s i j).symm)

/-! ### The composition -/

/-- The triple product square `(𝒳 i ×_𝒳 𝒳 j) ×_{𝒳 j} (𝒳 j ×_𝒳 𝒳 k)`. -/
noncomputable abbrev triSq (i j k : C.ι) : Bicategory.TwoCommSq (C.pr₂ i j) (C.pr₁ j k) :=
  twoFibreProductSquareAlgebraicStacks B S hS (C.pr₂ i j) (C.pr₁ j k)

/-- The triple product `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k`. -/
noncomputable abbrev X₃ (i j k : C.ι) : AlgebraicStacks.{u, w} B S hS := (C.triSq i j k).pt

/-- The scheme `N i j ×_{t, M j, s} N j k`. -/
noncomputable abbrev P (i j k : C.ι) : BigFppfOver B S hS := pullback (C.t i j) (C.s j k)

/-- The first projection of `N i j ×_{t, M j, s} N j k`. -/
noncomputable abbrev p₁ (i j k : C.ι) : C.P i j k ⟶ C.N i j := pullback.fst _ _

/-- The second projection of `N i j ×_{t, M j, s} N j k`. -/
noncomputable abbrev p₂ (i j k : C.ι) : C.P i j k ⟶ C.N j k := pullback.snd _ _

/-- `N i j ×_{t, M j, s} N j k` with its projections `p₁`, `p₂` is a pullback square. -/
theorem isPullback_P (i j k : C.ι) :
    IsPullback (C.p₁ i j k) (C.p₂ i j k) (C.t i j) (C.s j k) :=
  IsPullback.of_hasPullback _ _

/-- The Yoneda image of the pullback square `N i j ×_{t, M j, s} N j k` is a pullback square of
presheaves. -/
theorem isPullback_yoneda_P (i j k : C.ι) :
    IsPullback (yoneda.map (C.p₁ i j k)) (yoneda.map (C.p₂ i j k)) (yoneda.map (C.t i j))
      (yoneda.map (C.s j k)) :=
  (C.isPullback_P i j k).map yoneda

/-- The first projection `p₁ : N i j ×_{t, M j, s} N j k ⟶ N i j` is étale. -/
instance etale_p₁ (i j k : C.ι) : Etale ((BigFppfOver.toScheme B S hS).map (C.p₁ i j k)) :=
  MorphismProperty.of_isPullback (P := @Etale)
    ((C.isPullback_P i j k).map (BigFppfOver.toScheme B S hS)).flip inferInstance

/-- The square of presheaves `N i j ×_{M j} N j k`, read on the attached categories. -/
noncomputable abbrev PSq (i j k : C.ι) :
    Bicategory.TwoCommSq (associatedMap B S hS (yoneda.map (C.t i j))).1
      (associatedMap B S hS (yoneda.map (C.s j k))).1 :=
  fibredCategorySquare (C.isPullback_yoneda_P i j k).w

/-- The two composites `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ M j`, through `t i j` and through `s j k`, are
equal. -/
theorem X₃_comm (i j k : C.ι) :
    ((C.triSq i j k).fst.hom ≫ (C.φ i j).hom) ≫ (associatedMap B S hS (yoneda.map (C.t i j))).1 =
      ((C.triSq i j k).snd.hom ≫ (C.φ j k).hom) ≫
        (associatedMap B S hS (yoneda.map (C.s j k))).1 :=
  calc ((C.triSq i j k).fst.hom ≫ (C.φ i j).hom) ≫ (associatedMap B S hS (yoneda.map (C.t i j))).1
      = (C.triSq i j k).fst.hom ≫ ((C.φ i j).hom ≫
          (associatedMap B S hS (yoneda.map (C.t i j))).1) := discrete_assoc _ _ _
    _ = (C.triSq i j k).fst.hom ≫ ((C.pr₂ i j).hom ≫ (C.f j).hom) := by rw [φ_comp_t]
    _ = ((C.triSq i j k).fst.hom ≫ (C.pr₂ i j).hom) ≫ (C.f j).hom := (discrete_assoc _ _ _).symm
    _ = ((C.triSq i j k).snd.hom ≫ (C.pr₁ j k).hom) ≫ (C.f j).hom :=
          discrete_whisker (Bicategory.InducedBicategory.isoHom (C.triSq i j k).iso).hom _
    _ = (C.triSq i j k).snd.hom ≫ ((C.pr₁ j k).hom ≫ (C.f j).hom) := discrete_assoc _ _ _
    _ = (C.triSq i j k).snd.hom ≫ ((C.φ j k).hom ≫
          (associatedMap B S hS (yoneda.map (C.s j k))).1) := by rw [φ_comp_s]
    _ = ((C.triSq i j k).snd.hom ≫ (C.φ j k).hom) ≫
          (associatedMap B S hS (yoneda.map (C.s j k))).1 := (discrete_assoc _ _ _).symm

/-- The triple product, as a square over the cospan of `N i j ×_{M j} N j k`. -/
noncomputable abbrev X₃Sq (i j k : C.ι) :
    Bicategory.TwoCommSq (associatedMap B S hS (yoneda.map (C.t i j))).1
      (associatedMap B S hS (yoneda.map (C.s j k))).1 :=
  ⟨(C.X₃ i j k).val, (C.triSq i j k).fst.hom ≫ (C.φ i j).hom,
    (C.triSq i j k).snd.hom ≫ (C.φ j k).hom, eqToIso (C.X₃_comm i j k)⟩

/-- The moduli morphism of the triple product, `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ N i j ×_{M j} N j k`,
with its comparisons. -/
noncomputable def φ₃Pre (i j k : C.ι) : Bicategory.TwoCommSq.PreHom (C.X₃Sq i j k) (C.PSq i j k) :=
  Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_fibredCategorySquare (C.isPullback_yoneda_P i j k)) _

/-- The moduli morphism of the triple product. -/
noncomputable abbrev φ₃ (i j k : C.ι) :
    (C.X₃ i j k).val ⟶ fibredCategory B S hS (yoneda.obj (C.P i j k)) :=
  (C.φ₃Pre i j k).hom

/-- The composite of `φ₃ i j k` with `p₁` is the first projection of the triple product
followed by `φ i j`. -/
theorem φ₃_comp_p₁ (i j k : C.ι) :
    C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map (C.p₁ i j k))).1 =
      (C.triSq i j k).fst.hom ≫ (C.φ i j).hom :=
  (hom_eq_of_hom₂ B S hS (C.φ₃Pre i j k).isoFst.hom).symm

/-- The composite of `φ₃ i j k` with `p₂` is the second projection of the triple product
followed by `φ j k`. -/
theorem φ₃_comp_p₂ (i j k : C.ι) :
    C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map (C.p₂ i j k))).1 =
      (C.triSq i j k).snd.hom ≫ (C.φ j k).hom :=
  (hom_eq_of_hom₂ B S hS (C.φ₃Pre i j k).isoSnd.hom).symm

/-- The square `(𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k, φ₃, q₁)` over the cospan `(p₁, φ i j)`. -/
noncomputable abbrev leftSq (i j k : C.ι) :
    Bicategory.TwoCommSq (associatedMap B S hS (yoneda.map (C.p₁ i j k))).1 (C.φ i j).hom :=
  ⟨(C.X₃ i j k).val, C.φ₃ i j k, (C.triSq i j k).fst.hom, eqToIso (C.φ₃_comp_p₁ i j k)⟩

/-- **The moduli morphism of the triple product is a base change of that of `𝒳 i ×_𝒳 𝒳 j`:**
`𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k = (N i j ×_{M j} N j k) ×_{N i j} (𝒳 i ×_𝒳 𝒳 j)`. -/
noncomputable def isTwoFibreProduct_leftSq (i j k : C.ι) :
    Bicategory.IsTwoFibreProduct (C.leftSq i j k) := by
  refine Bicategory.isTwoFibreProduct_of_isTwoFibreProduct_paste' (Q := (C.PSq i j k).swap)
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_fibredCategorySquare (C.isPullback_yoneda_P i j k))) (C.leftSq i j k) ?_
  have h₀ := Bicategory.isTwoFibreProduct_paste (C.isTwoFibreProduct_square j k)
    (T := (C.triSq i j k).underlying.swap) (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_underlying_algebraicStacks B S hS (C.triSq i j k)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)))
  exact isTwoFibreProduct_congr_of_discrete' rfl (C.φ_comp_t i j).symm _ h₀
    (C.φ₃_comp_p₂ i j k).symm rfl _

/-- **The moduli morphism of the triple product is a categorical moduli space.** -/
theorem isCategoricalModuliSpace_φ₃ (i j k : C.ι) :
    IsCategoricalModuliSpace B S hS
      (schemeSpace (C.P i j k)) (C.φ₃ i j k) := by
  let a : (⟨yoneda.obj (C.P i j k), isAlgebraicSpace_yoneda B S hS (C.P i j k)⟩ :
      AlgebraicSpaces B S hS) ⟶ C.Nsp i j := ObjectProperty.homMk (yoneda.map (C.p₁ i j k))
  have ha : Space.IsFlat B S hS a.hom := (isFlat_yoneda_map_iff B S hS (C.p₁ i j k)).2 inferInstance
  exact isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
    (isUniformCategoricalModuliSpace_fst B S hS (C.isUniformCategoricalModuliSpace_φ i j)
      a ha (C.leftSq i j k) (C.isTwoFibreProduct_leftSq i j k))

/-- The square `(𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k, q₁ ≫ pr₁, q₂ ≫ pr₂)` over the cospan `(g i, g k)`. -/
noncomputable abbrev X₃ikSq (i j k : C.ι) : Bicategory.TwoCommSq (C.map i) (C.map k) :=
  ⟨C.X₃ i j k, (C.triSq i j k).fst ≫ C.pr₁ i j, (C.triSq i j k).snd ≫ C.pr₂ j k,
    Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso (C.triSq i j k).fst (C.pairSq i j).iso ≪≫
      (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso (C.triSq i j k).iso (C.map j) ≪≫
      Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso (C.triSq i j k).snd (C.pairSq j k).iso ≪≫
      (Bicategory.associator _ _ _).symm⟩

/-- The projection `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ 𝒳 i ×_𝒳 𝒳 k`, with its comparisons. -/
noncomputable def pr₁₃ (i j k : C.ι) :
    Bicategory.TwoCommSq.PreHom (C.X₃ikSq i j k) (C.pairSq i k) :=
  Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map k)) _

/-- There is a morphism `c : N i j ×_{t, M j, s} N j k ⟶ N i k` such that `φ₃ i j k` composed
with `c` agrees with the projection `𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ 𝒳 i ×_𝒳 𝒳 k` followed by
`φ i k`. -/
theorem exists_comp (i j k : C.ι) :
    ∃ c : C.P i j k ⟶ C.N i k,
      C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map c)).1 =
        (C.pr₁₃ i j k).hom.hom ≫ (C.φ i k).hom :=
  exists_hom_of_isCategoricalModuliSpace (C.isCategoricalModuliSpace_φ₃ i j k) _

/-- **The composition `comp i j k : N i j ×_{t, M j, s} N j k ⟶ N i k`.** -/
noncomputable def comp (i j k : C.ι) : C.P i j k ⟶ C.N i k := (C.exists_comp i j k).choose

/-- The composite of `φ₃ i j k` with `comp i j k` is the projection
`𝒳 i ×_𝒳 𝒳 j ×_𝒳 𝒳 k ⟶ 𝒳 i ×_𝒳 𝒳 k` followed by `φ i k`. -/
theorem φ₃_comp_comp (i j k : C.ι) :
    C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map (C.comp i j k))).1 =
      (C.pr₁₃ i j k).hom.hom ≫ (C.φ i k).hom :=
  (C.exists_comp i j k).choose_spec

/-- **Two morphisms out of `N i j ×_{M j} N j k` factoring the same 1-morphism are equal.** -/
theorem hom_ext_P {i j k : C.ι} {Y : BigFppfOver B S hS} (a b : C.P i j k ⟶ Y)
    (h : C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map a)).1 =
      C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map b)).1) : a = b := by
  have := eq_of_isCategoricalModuliSpace B S hS (C.isCategoricalModuliSpace_φ₃ i j k)
    (C.φ₃ i j k ≫ (associatedMap B S hS (yoneda.map b)).1)
    (ObjectProperty.homMk (yoneda.map a) :
      (⟨yoneda.obj (C.P i j k), isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩)
    (ObjectProperty.homMk (yoneda.map b)) ⟨eqToIso (by exact h)⟩ ⟨Iso.refl _⟩
  exact yoneda.map_injective (congrArg (fun k => k.hom) this)

/-- The composition is compatible with the source: `comp i j k ≫ s i k = p₁ ≫ s i j`. -/
theorem comp_comp_s (i j k : C.ι) : C.comp i j k ≫ C.s i k = C.p₁ i j k ≫ C.s i j := by
  refine C.hom_ext_P _ _ ?_
  rw [associatedMap_yoneda_comp, associatedMap_yoneda_comp]
  exact (discrete_comp_comp_eq (C.φ₃_comp_comp i j k) (C.φ_comp_s i k)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.pr₁₃ i j k).isoFst).inv _).trans
      (discrete_comp_comp_eq (C.φ₃_comp_p₁ i j k) (C.φ_comp_s i j)).symm)

/-- The composition is compatible with the target: `comp i j k ≫ t i k = p₂ ≫ t j k`. -/
theorem comp_comp_t (i j k : C.ι) : C.comp i j k ≫ C.t i k = C.p₂ i j k ≫ C.t j k := by
  refine C.hom_ext_P _ _ ?_
  rw [associatedMap_yoneda_comp, associatedMap_yoneda_comp]
  exact (discrete_comp_comp_eq (C.φ₃_comp_comp i j k) (C.φ_comp_t i k)).trans
    ((discrete_whisker (Bicategory.InducedBicategory.isoHom (C.pr₁₃ i j k).isoSnd).inv _).trans
      (discrete_comp_comp_eq (C.φ₃_comp_p₂ i j k) (C.φ_comp_t j k)).symm)

end KeelMoriCover

end AlgebraicGeometry.Stack

end
