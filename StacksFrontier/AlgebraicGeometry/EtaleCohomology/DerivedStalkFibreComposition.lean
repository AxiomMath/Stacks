module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedFibreSectionsIdentities
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricFibreBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres
public import StacksCore.Tactic.StacksAttribute

/-!
# The composition clause of Stacks 0GIX

Let `f : X ⟶ S` be a morphism of schemes, `K` an object of the unbounded derived category
`D(X_étale)` of abelian sheaves on the small étale site of `X`, and `s` a geometric point of `S`.
Stacks 0GIX constructs canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections` and
`AlgebraicGeometry.strictHenselizationSectionsToFibreSections`) and asserts, by Cohomology on
Sites, Remark 0E47, that their composite is the usual base change map
`(Rf_*K)_s ⟶ RΓ(X_s, K|_{X_s})`. This file proves that assertion.

## Main results

* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_comp_fibreSections` — the
  composition clause of Stacks 0GIX for the maps as this library constructs them (the registered
  form, for the maps as the source defines them, is
  `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange_comp` in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedStalkFibreBaseChangeMaps.lean`). The
  composite of the two canonical
  maps is the identification of the stalk at `s` with derived global sections on `s` of the inverse
  image (`AlgebraicGeometry.derivedGeometricStalkToPullbackSections`), followed by derived global
  sections on `s` of the derived base change map of Stacks 0A2A for the cartesian square defining
  the geometric fibre (`AlgebraicGeometry.geometricFibreDerivedBaseChangeAb`), followed by the
  identification `RΓ(s, Rq_* -) ≅ RΓ(X_s, -)` of Stacks 0D6H
  (`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsPushforwardIsoAb`). It is an equality of
  natural transformations on all of `D(X_étale)`, for an arbitrary morphism `f` and an arbitrary
  geometric point `s`.
* `AlgebraicGeometry.geometricFibreDerivedBaseChangeAb_fac` — the derived base change map of the
  geometric fibre, precomposed with the units, is the degreewise base change map
  `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` followed by the unit of `Rq_*`.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_conj_fac` — the same for the derived base
  change map of an arbitrary commutative square, conjugated by identifications of the inverse
  images, at an arbitrary coefficient universe.
* `Stacks.DerivedFunctor.conjDerivedBaseChange_fac` — the generic form of the last statement, for
  abstract abelian categories and functors.

## Implementation notes

*The proof.* Both sides are transformations out of `Rf_* ⋙ (-)_s`, a right derived functor of the
degreewise stalk of the direct image, so `CategoryTheory.Functor.rightDerived_ext` reduces the
clause to a component at a complex `J` after the unit
(`AlgebraicGeometry.stalkFibreComposition_app`). The left-hand side is put in normal form by
`AlgebraicGeometry.stalkSectionsUnit_comp_fibreSections_app`, the right-hand side by naturality of
the comparisons and the factorization properties of the three maps it is made of; the two
degreewise maps that remain are compared by
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb`, the
underived form of the clause (`AlgebraicGeometry.stalkFibreDegreewise_app`).

*Why the derived base change map is handled in two stages.* The derived base change map of
Stacks 0A2A and its characterization `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` are
universe polymorphic in the coefficient universe `max (u + 1) v`, and their statements carry the
sheafification instance `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`. At `v = u + 1`,
the coefficient universe of `Stacks.EtaleCohomology.smallEtalePullbackAb` and its companions,
instance search in this library finds a different proof of the same `HasSheafify` instance, and a
statement that mixes the two spellings around a concrete base change map is checked by the kernel
only after unfolding that map: a restatement of `etaleAbelianHomotopyBaseChange_app` at
`v = u + 1` exceeds the kernel's budget, while the identical restatement at a generic `v`, or with
the same `HasSheafify` proof inlined, checks at once. So every statement about the derived base
change map is made at a generic `v` (`etaleAbelianHomotopyBaseChange_app_eq_ofComp`,
`etaleAbelianDerivedBaseChange_conj_fac`), with the identifications of the inverse images
abstracted, and is only instantiated at `v = u + 1`; the instantiation is a substitution, which
the kernel checks without unfolding anything.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.DerivedFunctor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]

/-- **The degreewise action of a conjugated transformation.** If `β : P ⋙ R ⟶ N ⋙ Q` is
`β' : P ⋙ R' ⟶ N' ⋙ Q` conjugated by isomorphisms `a : R ≅ R'` and `b : N ≅ N'`, then on
homotopy categories its degreewise action is the action of `a`, followed by that of `β'` (read
through the two comparisons of the action of a composite with the composite of the actions) and
by the action of `b⁻¹` inside `Q`.

Stated with the conjugating isomorphisms and the equation `hβ` as parameters, so that a concrete
instance never unfolds them. -/
public theorem mapHomotopyCategoryOfComp_conj (P : A₁ ⥤ A₂) [P.Additive] (R R' : A₂ ⥤ A₃)
    [R.Additive] [R'.Additive] (N N' : A₁ ⥤ A₄) [N.Additive] [N'.Additive] (Q : A₄ ⥤ A₃)
    [Q.Additive] (a : R ≅ R') (b : N ≅ N') (β' : P ⋙ R' ⟶ N' ⋙ Q) (β : P ⋙ R ⟶ N ⋙ Q)
    (hβ : β = Functor.whiskerLeft P a.hom ≫ β' ≫ Functor.whiskerRight b.inv Q)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp (P ⋙ R) N Q β).app J =
      (NatTrans.mapHomotopyCategory a.hom (ComplexShape.up ℤ)).app
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        (mapHomotopyCategoryOfComp (P ⋙ R') N' Q β').app J ≫
        (Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory b.inv (ComplexShape.up ℤ)).app J) := by
  subst hβ
  simp only [mapHomotopyCategoryOfComp_app]
  congr 1

/-- The rearrangement carrying the derived base change map of the geometric fibre, precomposed
with the two units, to a degreewise map followed by the unit of the derived direct image. Stated
for bare morphisms, so that the concrete factors, spelled through definitionally equal but
syntactically different descriptions of one object, meet only through unification. -/
private theorem baseChange_rearrange {C C' : Type*} [Category C] [Category C'] (Rq : C' ⥤ C)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C} {E₀ E₁ E₂ E₃ : C'}
    {fi : P₀ ⟶ P₁} {su : P₁ ⟶ P₂} {b : P₂ ⟶ Rq.obj E₃} {ih : P₂ ⟶ P₃} {eb : P₃ ⟶ Rq.obj E₂}
    {iqi : E₂ ⟶ E₃} {ih0 : P₁ ⟶ P₄} {esu : P₄ ⟶ P₃} {qI : P₀ ⟶ P₅} {efi : P₅ ⟶ P₄}
    {qH : P₅ ⟶ P₆} {uq' : P₆ ⟶ Rq.obj E₀} {eqi : E₀ ⟶ E₂} {qx : E₀ ⟶ E₁} {z : E₁ ⟶ E₃}
    {qqx : P₆ ⟶ P₇} {uq : P₇ ⟶ Rq.obj E₁} {w : P₀ ⟶ P₇}
    (hc : b = ih ≫ eb ≫ Rq.map iqi) (hd : su ≫ ih = ih0 ≫ esu) (he : fi ≫ ih0 = qI ≫ efi)
    (hf : efi ≫ esu ≫ eb = qH ≫ uq' ≫ Rq.map eqi) (hg : eqi ≫ iqi = qx ≫ z)
    (hh : uq' ≫ Rq.map qx = qqx ≫ uq) (hY : qI ≫ qH ≫ qqx = w) :
    fi ≫ su ≫ b = w ≫ uq ≫ Rq.map z := by
  subst hc
  rw [reassoc_of% hd, reassoc_of% he, reassoc_of% hf, ← Rq.map_comp, hg, Rq.map_comp,
    reassoc_of% hh, ← reassoc_of% hY]

/-- The rearrangement carrying the right-hand side of the composition clause, precomposed with
the unit, to its normal form. Stated for bare morphisms, as `baseChange_rearrange`. -/
public theorem fibreBaseChange_rearrange {C C' E : Type*} [Category C] [Category C'] [Category E]
    (Rs : C ⥤ E) (Rq : C' ⥤ C)
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : E} {P₀ P₁ P₂ P₇ : C} {E₁ E₃ : C'}
    {stu : A₀ ⟶ A₁} {d₁ : A₁ ⟶ Rs.obj P₂} {b : P₂ ⟶ Rq.obj E₃} {io : Rs.obj (Rq.obj E₃) ⟶ A₂}
    {d₀ : A₀ ⟶ Rs.obj P₁} {su : P₁ ⟶ P₂} {φ : A₀ ⟶ A₃} {qg : A₃ ⟶ A₄} {uS : A₄ ⟶ Rs.obj P₀}
    {fi : P₀ ⟶ P₁} {w : P₀ ⟶ P₇} {uq : P₇ ⟶ Rq.obj E₁} {z : E₁ ⟶ E₃}
    {io0 : Rs.obj (Rq.obj E₁) ⟶ A₅} {RXz : A₅ ⟶ A₂} {qΓY : A₄ ⟶ A₆} {uS' : A₆ ⟶ Rs.obj P₇}
    {qc : A₆ ⟶ A₇} {uX : A₇ ⟶ A₅}
    (ha : stu ≫ d₁ = d₀ ≫ Rs.map su) (hb : d₀ = φ ≫ qg ≫ uS ≫ Rs.map fi)
    (hC : fi ≫ su ≫ b = w ≫ uq ≫ Rq.map z) (hi : Rs.map (Rq.map z) ≫ io = io0 ≫ RXz)
    (hj : uS ≫ Rs.map w = qΓY ≫ uS') (hk : uS' ≫ Rs.map uq ≫ io0 = qc ≫ uX) :
    stu ≫ d₁ ≫ Rs.map b ≫ io = φ ≫ qg ≫ qΓY ≫ qc ≫ uX ≫ RXz := by
  have hR : Rs.map fi ≫ Rs.map su ≫ Rs.map b = Rs.map w ≫ Rs.map uq ≫ Rs.map (Rq.map z) := by
    rw [← Rs.map_comp, ← Rs.map_comp, hC, Rs.map_comp, Rs.map_comp]
  rw [reassoc_of% ha, hb]
  simp only [Category.assoc]
  rw [reassoc_of% hR, hi, reassoc_of% hj, reassoc_of% hk]

section Generic

universe w₁ w₂ w₃ w₄

variable [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂] [HasDerivedCategory.{w₃} A₃]
  [HasDerivedCategory.{w₄} A₄]

/-- **The derived base change map, conjugated, at a complex: the generic form.** Let
`F : A₁ ⥤ A₂` and `Q : A₄ ⥤ A₃` be additive, and let `Ps, Ps' : A₂ ⥤ A₃` and
`Px, Px' : A₁ ⥤ A₄` be exact, with identifications `ιs : Ps ≅ Ps'` and `ιx : Px ≅ Px'` and
identifications `ιsD`, `ιxD` of their actions on derived categories which are compatible with
them on the image of `DerivedCategory.Qh` (`he`, `hg`). Let `BCD : RF ⋙ Ps'_D ⟶ Px'_D ⋙ RQ` be
characterized, through the units `uF` and `uQ` of derivations `RF` of `F` and `RQ` of `Q`, by a
degreewise comparison `hBC` which is the degreewise action of `β'` (`hfac`, `hhBC`). Then the
conjugate `ιsD ≫ BCD ≫ ιxD⁻¹`, precomposed with the units, is the degreewise action of the
conjugate `β` of `β'` followed by the unit of `RQ`.

Everything concrete enters through the hypotheses, so an instance of this lemma never unfolds a
concrete base change map. -/
public theorem conjDerivedBaseChange_fac
    (F : A₁ ⥤ A₂) [F.Additive] (Ps Ps' : A₂ ⥤ A₃) [Ps.Additive] [PreservesFiniteLimits Ps]
    [PreservesFiniteColimits Ps] [Ps'.Additive] [PreservesFiniteLimits Ps']
    [PreservesFiniteColimits Ps'] (Px Px' : A₁ ⥤ A₄) [Px.Additive] [PreservesFiniteLimits Px]
    [PreservesFiniteColimits Px] [Px'.Additive] [PreservesFiniteLimits Px']
    [PreservesFiniteColimits Px'] (Q : A₄ ⥤ A₃) [Q.Additive]
    (ιs : Ps ≅ Ps') (ιx : Px ≅ Px') (ιsD : Ps.mapDerivedCategory ≅ Ps'.mapDerivedCategory)
    (ιxD : Px.mapDerivedCategory ≅ Px'.mapDerivedCategory)
    (he : ∀ M : HomotopyCategory A₂ (ComplexShape.up ℤ),
      Ps.mapDerivedCategoryFactorsh.inv.app M ≫ ιsD.hom.app (DerivedCategory.Qh.obj M) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ιs.hom (ComplexShape.up ℤ)).app M) ≫
          Ps'.mapDerivedCategoryFactorsh.inv.app M)
    (hg : ∀ J : HomotopyCategory A₁ (ComplexShape.up ℤ),
      Px'.mapDerivedCategoryFactorsh.inv.app J ≫ ιxD.inv.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app J) ≫
          Px.mapDerivedCategoryFactorsh.inv.app J)
    (RF : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (RQ : DerivedCategory A₄ ⥤ DerivedCategory A₃)
    (uQ : Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RQ)
    (β' : F ⋙ Ps' ⟶ Px' ⋙ Q)
    (hBC : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Ps'.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      Px'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Q.mapHomotopyCategory (ComplexShape.up ℤ))
    (hhBC : ∀ K : HomotopyCategory A₁ (ComplexShape.up ℤ), hBC.app K =
      (mapHomotopyCategoryOfComp (F ⋙ Ps') Px' Q β').app K)
    (BCD : RF ⋙ Ps'.mapDerivedCategory ⟶ Px'.mapDerivedCategory ⋙ RQ)
    (hfac : ∀ K : HomotopyCategory A₁ (ComplexShape.up ℤ),
      Ps'.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          Ps'.mapDerivedCategory.map (uF.app K) ≫ BCD.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map (hBC.app K) ≫
          uQ.app ((Px'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          RQ.map (Px'.mapDerivedCategoryFactorsh.inv.app K))
    (β : F ⋙ Ps ⟶ Px ⋙ Q)
    (hβ : β = Functor.whiskerLeft F ιs.hom ≫ β' ≫ Functor.whiskerRight ιx.inv Q)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    Ps.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        Ps.mapDerivedCategory.map (uF.app J) ≫
        (ιsD.hom.app (RF.obj (DerivedCategory.Qh.obj J)) ≫ BCD.app (DerivedCategory.Qh.obj J) ≫
          RQ.map (ιxD.inv.app (DerivedCategory.Qh.obj J))) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp (F ⋙ Ps) Px Q β).app J) ≫
        uQ.app ((Px.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        RQ.map (Px.mapDerivedCategoryFactorsh.inv.app J) := by
  refine baseChange_rearrange RQ rfl (ιsD.hom.naturality (uF.app J))
    (he ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) (hfac J) (hg J)
    (uQ.naturality ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app J)).symm ?_
  rw [mapHomotopyCategoryOfComp_conj F Ps Ps' Px Px' Q ιs ιx β' β hβ J, hhBC J]
  exact (congrArg (_ ≫ ·) (DerivedCategory.Qh.map_comp _ _).symm).trans
    (DerivedCategory.Qh.map_comp _ _).symm

omit [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃]
  [HasDerivedCategory A₄] in
/-- The degreewise action of a transformation `τ : F ⋙ G ⟶ G' ⋙ F'`, read between the two
comparisons of the action of a composite with the composite of the actions, is
`Stacks.DerivedFunctor.mapHomotopyCategoryOfComp` of `τ` precomposed with the first comparison,
which is an identity. Stated for an arbitrary `τ`, so that an instance never unfolds it. -/
private theorem compIso_comp_eq_ofComp (F : A₁ ⥤ A₂) [F.Additive] (G : A₂ ⥤ A₃) [G.Additive]
    (G' : A₁ ⥤ A₄) [G'.Additive] (F' : A₄ ⥤ A₃) [F'.Additive] (τ : F ⋙ G ⟶ G' ⋙ F')
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app J ≫
        (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app J ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G' ⋙ F')) (ComplexShape.up ℤ)).inv.app J =
      (mapHomotopyCategoryOfComp (F ⋙ G) G' F' τ).app J := by
  rw [mapHomotopyCategoryOfComp_app]
  change (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map (𝟙 _) ≫
      (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Absorbing an associator between a left whiskering and a right whiskering. -/
private theorem whiskerLeft_comp_associator_inv_comp_whiskerRight {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E] (P : C ⥤ D) {Γ : D ⥤ E}
    {I : D ⥤ D'} {Γ' : D' ⥤ E} {Q : C ⥤ D'} (r : Γ ⟶ I ⋙ Γ') (e : P ⋙ I ⟶ Q) :
    Functor.whiskerLeft P r ≫ (Functor.associator P I Γ').inv ≫ Functor.whiskerRight e Γ' =
      Functor.whiskerLeft P r ≫ Functor.whiskerRight e Γ' := by
  ext
  simp

/-- Replacing three middle factors by their composite, in a composite of five. Stated for bare
morphisms so that it applies by unification to factors spelled differently. -/
public theorem comp_three_middle {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    (φ : A₀ ⟶ A₁) {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {c : A₃ ⟶ A₄} {x : A₁ ⟶ A₄} (d : A₄ ⟶ A₅)
    (h : a ≫ b ≫ c = x) : φ ≫ x ≫ d = φ ≫ a ≫ b ≫ c ≫ d := by
  rw [← h]
  simp only [Category.assoc]

/-- Absorbing an identity after the first factor on both sides of an equation. -/
public theorem comp_id_comp_eq {C : Type*} [Category C] {A₀ A₁ A₂ : C} (φ : A₀ ⟶ A₁)
    {x y : A₁ ⟶ A₂} (h : φ ≫ x = φ ≫ y) : (φ ≫ 𝟙 A₁) ≫ x = (φ ≫ 𝟙 A₁) ≫ y := by
  rw [Category.comp_id, h]

end Generic

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {X₀ Y₀ X₀' Y₀' : Scheme.{u}} (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀' ⟶ Y₀) (g₀' : X₀' ⟶ X₀)
  (f₀' : X₀' ⟶ Y₀') (h₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive in
/-- The degreewise base change comparison at a complex, as the degreewise action of the
underived base change map. -/
public theorem etaleAbelianHomotopyBaseChange_app_eq_ofComp (J : HomotopyCategory
      (Sheaf X₀.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)) :
    (etaleAbelianHomotopyBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀).app J =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (etaleAbelianDirectImage.{u, v} f₀ ⋙ etaleAbelianInverseImage.{u, v} g₀)
        (etaleAbelianInverseImage.{u, v} g₀') (etaleAbelianDirectImage.{u, v} f₀')
        (etaleAbelianBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀)).app J :=
  (etaleAbelianHomotopyBaseChange_app.{u, v} f₀ g₀ g₀' f₀' h₀ J).trans
    (Stacks.DerivedFunctor.compIso_comp_eq_ofComp _ _ _ _ _ J)

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive in
/-- **The derived base change map of a commutative square, conjugated, at a complex.** For exact
functors `Ps` and `Px` identified (`ιs`, `ιx`) with the inverse images along the two horizontal
legs of the square, and identifications `ιsD`, `ιxD` of their actions on derived categories which
are compatible with them on the image of `DerivedCategory.Qh`, the derived base change map of
Stacks 0A2A conjugated by `ιsD` and `ιxD`, precomposed with the units, is the degreewise action of
the conjugated underived base change map `β` followed by the unit of the derived direct image. -/
public theorem etaleAbelianDerivedBaseChange_conj_fac
    (Ps : Sheaf Y₀.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf Y₀'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Ps.Additive]
    [PreservesFiniteLimits Ps] [PreservesFiniteColimits Ps]
    (Px : Sheaf X₀.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X₀'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Px.Additive]
    [PreservesFiniteLimits Px] [PreservesFiniteColimits Px]
    (ιs : Ps ≅ etaleAbelianInverseImage.{u, v} g₀) (ιx : Px ≅ etaleAbelianInverseImage.{u, v} g₀')
    (ιsD : Ps.mapDerivedCategory ≅ (etaleAbelianInverseImage.{u, v} g₀).mapDerivedCategory)
    (ιxD : Px.mapDerivedCategory ≅ (etaleAbelianInverseImage.{u, v} g₀').mapDerivedCategory)
    (he : ∀ M, Ps.mapDerivedCategoryFactorsh.inv.app M ≫ ιsD.hom.app (DerivedCategory.Qh.obj M) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ιs.hom (ComplexShape.up ℤ)).app M) ≫
          (etaleAbelianInverseImage.{u, v} g₀).mapDerivedCategoryFactorsh.inv.app M)
    (hg : ∀ J, (etaleAbelianInverseImage.{u, v} g₀').mapDerivedCategoryFactorsh.inv.app J ≫
          ιxD.inv.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app J) ≫
          Px.mapDerivedCategoryFactorsh.inv.app J)
    (β : etaleAbelianDirectImage.{u, v} f₀ ⋙ Ps ⟶ Px ⋙ etaleAbelianDirectImage.{u, v} f₀')
    (hβ : β = Functor.whiskerLeft _ ιs.hom ≫ etaleAbelianBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀ ≫
      Functor.whiskerRight ιx.inv _)
    (J : HomotopyCategory (Sheaf X₀.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) :
    Ps.mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianDirectImage.{u, v} f₀).mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        Ps.mapDerivedCategory.map ((etaleAbelianDerivedDirectImageUnit.{u, v} f₀).app J) ≫
        (ιsD.hom.app ((etaleAbelianDerivedDirectImage.{u, v} f₀).obj (DerivedCategory.Qh.obj J)) ≫
          (etaleAbelianDerivedBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀).app (DerivedCategory.Qh.obj J) ≫
          (etaleAbelianDerivedDirectImage.{u, v} f₀').map
            (ιxD.inv.app (DerivedCategory.Qh.obj J))) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (etaleAbelianDirectImage.{u, v} f₀ ⋙ Ps) Px (etaleAbelianDirectImage.{u, v} f₀')
          β).app J) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, v} f₀').app
          ((Px.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f₀').map (Px.mapDerivedCategoryFactorsh.inv.app J) :=
  Stacks.DerivedFunctor.conjDerivedBaseChange_fac (etaleAbelianDirectImage.{u, v} f₀) Ps
    (etaleAbelianInverseImage.{u, v} g₀) Px (etaleAbelianInverseImage.{u, v} g₀')
    (etaleAbelianDirectImage.{u, v} f₀') ιs ιx ιsD ιxD he hg
    (etaleAbelianDerivedDirectImage.{u, v} f₀) (etaleAbelianDerivedDirectImageUnit.{u, v} f₀)
    (etaleAbelianDerivedDirectImage.{u, v} f₀') (etaleAbelianDerivedDirectImageUnit.{u, v} f₀')
    (etaleAbelianBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀)
    (etaleAbelianHomotopyBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀)
    (etaleAbelianHomotopyBaseChange_app_eq_ofComp.{u, v} f₀ g₀ g₀' f₀' h₀)
    (etaleAbelianDerivedBaseChange.{u, v} f₀ g₀ g₀' f₀' h₀)
    (etaleAbelianDerivedBaseChange_fac.{u, v} f₀ g₀ g₀' f₀' h₀) β hβ J

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)


/-- **The derived base change map of the geometric fibre, at a complex.** Precomposed with the
identification of the two actions of the inverse image to the geometric point and with the unit
of the derivation of direct image, the derived base change map of the cartesian square defining
the geometric fibre is the degreewise base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` followed by the unit of the derivation of direct
image along the structure morphism of the fibre. -/
theorem geometricFibreDerivedBaseChangeAb_fac
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtalePullbackAb s.hom).mapDerivedCategoryFactorsh.inv.app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPullbackAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (geometricFibreDerivedBaseChangeAb f s).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb f ⋙ smallEtalePullbackAb s.hom)
          (smallEtalePullbackAb (geometricFibreToSource f s))
          (smallEtalePushforwardAb (geometricFibreToPoint f s))
          (smallEtaleBaseChangeAb s.hom f (geometricFibreToPoint f s)
            (geometricFibreToSource f s) pullback.condition.symm)).app J) ≫
        (smallEtaleDerivedPushforwardAbUnit (geometricFibreToPoint f s)).app
          ((Functor.mapHomotopyCategory (smallEtalePullbackAb (geometricFibreToSource f s))
            (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s)).map
          ((smallEtalePullbackAb (geometricFibreToSource f s)).mapDerivedCategoryFactorsh.inv.app
            J) := by
  refine (congrArg (fun t => _ ≫ _ ≫ t)
    (geometricFibreDerivedBaseChangeAb_app f s (DerivedCategory.Qh.obj J))).trans ?_
  exact etaleAbelianDerivedBaseChange_conj_fac.{u, u + 1} f s.hom (geometricFibreToSource f s)
    (geometricFibreToPoint f s) pullback.condition _ _
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage s.hom)
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage (geometricFibreToSource f s))
    (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage s.hom)
    (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage (geometricFibreToSource f s))
    (mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso s.hom)
    (mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso_inv
      (geometricFibreToSource f s)) _
    (smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange s.hom f (geometricFibreToPoint f s)
      (geometricFibreToSource f s) pullback.condition.symm) J

/-- **The underived core of the composition clause, in the shape the derived maps present it.**
The transformation out of which the composite of the two derived maps of Stacks 0GIX is descended
is the base change map of the cartesian square defining the geometric fibre, read on global
sections over the geometric point. -/
theorem stalkFibreDegreewise_eq :
    pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
        Functor.whiskerLeft (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleGlobalSectionsRestrictionAb
            (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (geometricFibrePullbackAbCompIso B hS f s).hom
          (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}) =
      Functor.whiskerLeft (smallEtalePushforwardAb f)
          (geometricStalkToPullbackSectionsAb s.hom) ≫
        Functor.whiskerRight
          (smallEtaleBaseChangeAb s.hom f (geometricFibreToPoint f s)
            (geometricFibreToSource f s) pullback.condition.symm)
          (Sheaf.Γ (smallEtaleTopology s.source) Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb (geometricFibreToSource f s))
          (smallEtalePushforwardGammaIsoAb (geometricFibreToPoint f s)).hom := by
  have h := (Stacks.DerivedFunctor.whiskerLeft_comp_associator_inv_comp_whiskerRight
    (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
    (smallEtaleGlobalSectionsRestrictionAb
      (geometricFibreToStrictHenselizationBaseChange B hS f s))
    (geometricFibrePullbackAbCompIso B hS f s).hom).trans
    (fibreSectionsRestrictionAb_eq B hS f s).symm
  exact (congrArg (pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫ ·) h).trans
    (pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb B hS f s)

/-- **The degreewise part of the right-hand side of the composition clause.** The degreewise
comparison of the stalk with sections on the geometric point, the degreewise base change map of
the geometric fibre inside sections over the point, and the identification of sections of a direct
image compose to the degreewise action of the transformation out of which the left-hand side is
descended. -/
theorem stalkFibreDegreewise_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb s.hom) (smallEtalePullbackAb s.hom)
          (Sheaf.Γ (smallEtaleTopology s.source) Ab.{u + 1})
          (geometricStalkToPullbackSectionsAb s.hom)).app
          ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategory (Sheaf.Γ (smallEtaleTopology s.source) Ab.{u + 1})
            (.up ℤ)).map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
              (smallEtalePushforwardAb f ⋙ smallEtalePullbackAb s.hom)
              (smallEtalePullbackAb (geometricFibreToSource f s))
              (smallEtalePushforwardAb (geometricFibreToPoint f s))
              (smallEtaleBaseChangeAb s.hom f (geometricFibreToPoint f s)
                (geometricFibreToSource f s) pullback.condition.symm)).app J)) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (smallEtalePushforwardGammaIsoAb (geometricFibreToPoint f s)) (.up ℤ)).hom.app
          ((Functor.mapHomotopyCategory (smallEtalePullbackAb (geometricFibreToSource f s))
            (.up ℤ)).obj J)) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
        (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
        (smallEtalePullbackAb (geometricFibreToSource f s))
        (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1})
        (pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
          Functor.whiskerLeft
              (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
              (smallEtaleGlobalSectionsRestrictionAb
                (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
            (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (geometricFibrePullbackAbCompIso B hS f s).hom
              (Sheaf.Γ (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}))).app J) := by
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_three, stalkFibreDegreewise_eq]

/-- **The composition clause of Stacks 0GIX, at a complex.** Precomposed with the unit of the
derivation of direct image, the composite of the two canonical maps of Stacks 0GIX and the usual
base change map agree at the image of every complex. -/
theorem stalkFibreComposition_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
          (DerivedCategory.Qh.obj J) ≫
        (strictHenselizationSectionsToFibreSections B hS f s).app (DerivedCategory.Qh.obj J) =
      (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (derivedGeometricStalkToPullbackSections s.hom).app
          ((smallEtaleDerivedPushforwardAb f).obj (DerivedCategory.Qh.obj J)) ≫
        (smallEtaleDerivedGlobalSections s.source).map
          ((geometricFibreDerivedBaseChangeAb f s).app (DerivedCategory.Qh.obj J)) ≫
        (smallEtaleDerivedGlobalSectionsPushforwardIsoAb (geometricFibreToPoint f s)).hom.app
          ((smallEtaleDerivedPullbackAb (geometricFibreToSource f s)).obj
            (DerivedCategory.Qh.obj J)) := by
  have hL := (reassoc_of% (derivedPushforwardStalkToStrictHenselizationSections_fac_app
    B hS f s J)) ((strictHenselizationSectionsToFibreSections B hS f s).app
      (DerivedCategory.Qh.obj J))
  refine hL.trans ((stalkSectionsUnit_comp_fibreSections_app B hS f s J).trans ?_)
  have hR := Stacks.DerivedFunctor.fibreBaseChange_rearrange
    (smallEtaleDerivedGlobalSections s.source)
    (smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s))
    ((derivedGeometricStalkToPullbackSections s.hom).naturality
      ((smallEtaleDerivedPushforwardAbUnit f).app J))
    (derivedGeometricStalkSections_app s
      ((Functor.mapHomotopyCategory (smallEtalePushforwardAb f) (.up ℤ)).obj J))
    (geometricFibreDerivedBaseChangeAb_fac f s J)
    ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb (geometricFibreToPoint f s)).hom.naturality
      ((smallEtalePullbackAb (geometricFibreToSource f s)).mapDerivedCategoryFactorsh.inv.app J))
    ((smallEtaleDerivedGlobalSectionsUnit s.source).naturality
      ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePushforwardAb f ⋙ smallEtalePullbackAb s.hom)
          (smallEtalePullbackAb (geometricFibreToSource f s))
          (smallEtalePushforwardAb (geometricFibreToPoint f s))
          (smallEtaleBaseChangeAb s.hom f (geometricFibreToPoint f s)
            (geometricFibreToSource f s) pullback.condition.symm)).app J)).symm
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app (geometricFibreToPoint f s)
      ((Functor.mapHomotopyCategory (smallEtalePullbackAb (geometricFibreToSource f s))
        (.up ℤ)).obj J))
  refine Eq.trans ?_ hR.symm
  exact Stacks.DerivedFunctor.comp_three_middle _ _ (stalkFibreDegreewise_app B hS f s J)

/-- **Stacks 0GIX, the composition clause.** For a morphism of schemes `f : X ⟶ S` and a
geometric point `s` of `S`, the composite of the two canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

is the usual base change map `(Rf_*K)_s ⟶ RΓ(X_s, K|_{X_s})`: the identification of the stalk at
`s` with global sections on `s` of the inverse image, followed by global sections on `s` of the
derived base change map `s⁻¹Rf_*K ⟶ Rq_*(K|_{X_s})` of Stacks 0A2A for the cartesian square
defining the geometric fibre (`q : X_s ⟶ s` its structure morphism), and by the identification
`RΓ(s, Rq_* -) ≅ RΓ(X_s, -)` of Stacks 0D6H. This holds as an equality of natural transformations
on the whole unbounded derived category `D(X_étale)`; nothing is assumed of `f` or of `s`.

Both sides are maps out of the stalk of the derived direct image, which is a right derived functor
of the stalk of the direct image, so they agree as soon as they agree after the unit, which is
`AlgebraicGeometry.stalkFibreComposition_app`.

The Stacks 0GIX registration of this clause is on
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsViaBaseChange_comp`, the
same statement for the two maps as the source defines them, which is deduced from this one. -/
theorem derivedPushforwardStalkToStrictHenselizationSections_comp_fibreSections :
    derivedPushforwardStalkToStrictHenselizationSections B hS f s ≫
        strictHenselizationSectionsToFibreSections B hS f s =
      Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
          (derivedGeometricStalkToPullbackSections s.hom) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (geometricFibreDerivedBaseChangeAb f s)
          (smallEtaleDerivedGlobalSections s.source) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb (geometricFibreToSource f s))
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb (geometricFibreToPoint f s)).hom := by
  refine Functor.rightDerived_ext
    (smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom)
    (Functor.whiskerRight (smallEtaleDerivedPushforwardAbUnit f)
        (smallEtaleDerivedStalkAb s.hom) ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  refine NatTrans.ext (funext fun J => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  exact Stacks.DerivedFunctor.comp_id_comp_eq _ (stalkFibreComposition_app B hS f s J)

end AlgebraicGeometry

end
