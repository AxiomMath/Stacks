module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.SchemesOverCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemeFpqcSite
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale

/-!
# The total space of a presheaf on the test schemes over an algebraic space

Let `Y` be an algebraic space over a scheme `S` of a big fppf site.  The representability
statements of the `Quot` chapter (Stacks 08JX, 08JY, 08K6, 08K9) concern functors on the test
schemes over `Y`, `AlgebraicGeometry.Space.SchemesOver Y`.  This file passes between such a
functor and a presheaf on the big fppf site of `S` lying over `Y`: the *total space* of
`R : (SchemesOver Y)ᵒᵖ ⥤ Type u` has as sections over `V` the pairs of a section `y` of `Y` over
`V` and an element of `R` at the test scheme `(V, y)`.

## Main definitions

* `AlgebraicGeometry.Space.schemesOverEquivYoneda`: the test schemes over `Y` are the costructured
  arrows of the Yoneda embedding into the underlying presheaf of `Y`.
* `AlgebraicGeometry.Space.presheafPointsOver`: the points of a presheaf `H` over `Y` on the test
  schemes over `Y`, the counterpart of `AlgebraicGeometry.Space.spacePointsOver` for a presheaf
  not yet known to be an algebraic space.
* `AlgebraicGeometry.Space.totalSpace` and `AlgebraicGeometry.Space.totalSpaceProj`: the total
  space of `R` and its projection to `Y`.
* `AlgebraicGeometry.Space.pointsIsoToHom`: the morphism `yoneda.obj W ⟶ H` attached to an
  identification of the points of `H` over `Y`, restricted to a test scheme `T`, with the points
  of a scheme `W` over `T`.

## Main results

* `AlgebraicGeometry.Space.presheafPointsOverTotalSpaceIso`: the points over `Y` of the total
  space of `R` are `R`.
* `AlgebraicGeometry.Space.isPullback_pointsIsoToHom`: in that situation `W` is the fibre
  product `H ×_Y T`.
* `AlgebraicGeometry.Space.testProj_cocontinuous_fpqc`: the projection from the test schemes over
  `Y` to the big fppf site is cocontinuous for the fpqc topologies, and
  `AlgebraicGeometry.Space.functorPullback_testProj_mem_fpqcTopology` its consequence for the big
  fppf topology.
* `AlgebraicGeometry.Space.isSheaf_of_isSheaf_presheafPointsOver`: a presheaf over `Y` whose
  points over `Y` form an fpqc sheaf on the test schemes is an fppf sheaf.

## Implementation notes

The total space is Mathlib's `CategoryTheory.OverPresheafAux.yonedaCollectionPresheaf`, one half
of the equivalence `CategoryTheory.overEquivPresheafCostructuredArrow` between presheaves over a
presheaf `A` and presheaves on the costructured arrows of the Yoneda embedding into `A`; its
counit `CategoryTheory.OverPresheafAux.counitAux` is the identification of the points over `Y`
with `R`.  Reusing it avoids redoing the dependent-type bookkeeping of the sigma type of pairs.

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Equivalence

variable (Y : AlgebraicSpaces B S hS)

/-- A test scheme over `Y` read as a costructured arrow of the Yoneda embedding into the
underlying presheaf of `Y`. -/
@[simps]
def schemesOverToYoneda :
    SchemesOver Y ⥤ CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ _) Y.1 where
  obj T := CostructuredArrow.mk T.hom.hom
  map g := CostructuredArrow.homMk g.left
    (congrArg InducedCategory.Hom.hom (CostructuredArrow.w g))

/-- A costructured arrow of the Yoneda embedding into the underlying presheaf of `Y`, read as a
test scheme over `Y`. -/
@[simps]
def yonedaToSchemesOver :
    CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ _) Y.1 ⥤ SchemesOver Y where
  obj s := CostructuredArrow.mk (Y := s.left) (ObjectProperty.homMk s.hom :
    (schemeSpaceFunctor B S hS).obj s.left ⟶ Y)
  map g := CostructuredArrow.homMk g.left (ObjectProperty.hom_ext _ (CostructuredArrow.w g))

/-- The test schemes over `Y` are the costructured arrows of the Yoneda embedding into the
underlying presheaf of `Y`. -/
def schemesOverEquivYoneda :
    SchemesOver Y ≌ CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ _) Y.1 where
  functor := schemesOverToYoneda Y
  inverse := yonedaToSchemesOver Y
  unitIso := NatIso.ofComponents (fun T => CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun T => CostructuredArrow.isoMk (Iso.refl _))

end Equivalence

section PointsOver

variable {Y : AlgebraicSpaces B S hS}

/-- **The points of a presheaf over `Y` on the test schemes over `Y`**: for a test scheme `T`
over `Y`, the sections of `H` over the underlying scheme of `T` lying over the section of `Y`
that `T` is.  This is `AlgebraicGeometry.Space.spacePointsOver` for a presheaf which is not yet
known to be an algebraic space, read through the costructured arrows of the Yoneda embedding. -/
def presheafPointsOver {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : H ⟶ Y.1) :
    (SchemesOver Y)ᵒᵖ ⥤ Type u :=
  (schemesOverToYoneda Y).op ⋙ OverPresheafAux.restrictedYonedaObj p

/-- The points over `Y` of an algebraic space over `Y` are its points as a presheaf over the
underlying presheaf of `Y`. -/
def spacePointsOverIsoPresheafPointsOver {H : AlgebraicSpaces B S hS} (p : H ⟶ Y) :
    spacePointsOver p ≅ presheafPointsOver p.hom :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun x => ⟨x.1, ⟨x.2⟩⟩
        invFun := fun x => ⟨x.1, x.2.app⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end PointsOver

section TotalSpace

variable {Y : AlgebraicSpaces B S hS} (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)

/-- `R` transported to the costructured arrows of the Yoneda embedding. -/
abbrev yonedaPresheaf : (CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ _) Y.1)ᵒᵖ ⥤ Type u :=
  (yonedaToSchemesOver Y).op ⋙ R

/-- **The total space of a presheaf on the test schemes over `Y`**: the presheaf on the big fppf
site of `S` whose sections over `V` are the pairs of a section `y` of `Y` over `V` and an element
of `R` at the test scheme `(V, y)`. -/
def totalSpace : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  OverPresheafAux.yonedaCollectionPresheaf Y.1 (yonedaPresheaf R)

/-- The projection of the total space to `Y`. -/
def totalSpaceProj : totalSpace R ⟶ Y.1 :=
  OverPresheafAux.yonedaCollectionPresheafToA (yonedaPresheaf R)

/-- **The points over `Y` of the total space of `R` are `R`.** -/
def presheafPointsOverTotalSpaceIso : presheafPointsOver (totalSpaceProj R) ≅ R :=
  ((schemesOverToYoneda Y).op.isoWhiskerLeft (OverPresheafAux.counitAux (yonedaPresheaf R))).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (schemesOverEquivYoneda Y).unitIso).symm R ≪≫
    R.leftUnitor

end TotalSpace

section Pullback

variable {Y : AlgebraicSpaces B S hS} {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : H ⟶ Y.1)
  (T : SchemesOver Y) {W : BigFppfOver B S hS} (w : W ⟶ T.left)

/-- The test scheme over `T.left` given by a morphism `t : V ⟶ W` followed by `w`. -/
abbrev composedTest {V : BigFppfOver B S hS} (t : V ⟶ W) :
    SchemesOver ((schemeSpaceFunctor B S hS).obj T.left) :=
  CostructuredArrow.mk (Y := V) ((schemeSpaceFunctor B S hS).map (t ≫ w))

/-- The point of `W` over `T.left`, at the test scheme `composedTest T w t`, that `t` is. -/
def composedTestPoint {V : BigFppfOver B S hS} (t : V ⟶ W) :
    spacePointsOverObj ((schemeSpaceFunctor B S hS).map w) (composedTest T w t) :=
  ⟨t, (yonedaEquiv_yoneda_map (t ≫ w)).symm⟩

variable {p T w}
variable (φ : spacePointsOver ((schemeSpaceFunctor B S hS).map w) ≅
      (CostructuredArrow.map T.hom).op ⋙ presheafPointsOver p)

/-- The morphism `yoneda.obj W ⟶ H` attached to an identification of the points of `W` over
`T.left` with the points of `H` over `Y` on the test schemes over `T.left`. -/
def pointsIsoToHom : yoneda.obj W ⟶ H where
  app V := ↾fun t => (φ.hom.app (op (composedTest T w t)) (composedTestPoint T w t)).1
  naturality V V' a := by
    ext t
    let g : composedTest T w (a.unop ≫ t) ⟶ composedTest T w t :=
      CostructuredArrow.homMk a.unop (by
        apply ObjectProperty.hom_ext
        simp [composedTest])
    exact congrArg Subtype.val (NatTrans.naturality_apply φ.hom g.op (composedTestPoint T w t))

/-- The value of `pointsIsoToHom φ` at `t : V ⟶ W` is the point of `H` that `φ` attaches to
`composedTestPoint T w t`. -/
theorem pointsIsoToHom_app (V : BigFppfOver B S hS) (t : V ⟶ W) :
    (pointsIsoToHom φ).app (op V) t =
      (φ.hom.app (op (composedTest T w t)) (composedTestPoint T w t)).1 := rfl

/-- The test scheme over `T.left` given by a morphism `s : V ⟶ T.left`. -/
abbrev mapTest {V : BigFppfOver B S hS} (s : V ⟶ T.left) :
    SchemesOver ((schemeSpaceFunctor B S hS).obj T.left) :=
  CostructuredArrow.mk (Y := V) ((schemeSpaceFunctor B S hS).map s)

/-- The identity of `V`, as a morphism between the test schemes of two equal morphisms. -/
def mapTestEqHom {V : BigFppfOver B S hS} {s s' : V ⟶ T.left} (h : s = s') :
    mapTest s ⟶ mapTest s' :=
  CostructuredArrow.homMk (𝟙 V) (by subst h; simp)

include φ in
/-- The value of `pointsIsoToHom φ` at `t`, computed at any test scheme whose structure morphism
is `t ≫ w`. -/
theorem pointsIsoToHom_app_eq {V : BigFppfOver B S hS} (s : V ⟶ T.left) (t : V ⟶ W)
    (ht : (yoneda.map w).app (op V) t = testPoint (mapTest s)) :
    (pointsIsoToHom φ).app (op V) t = (φ.hom.app (op (mapTest s)) ⟨t, ht⟩).1 := by
  have hs : t ≫ w = s := ht.trans (yonedaEquiv_yoneda_map s)
  have h := congrArg Subtype.val (NatTrans.naturality_apply φ.hom (mapTestEqHom hs).op ⟨t, ht⟩)
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · exact FunctorToTypes.map_id_apply H _

/-- **A representing object of the points over `Y` restricted to a test scheme gives a pullback
square.**  If the points of `H` over `Y`, on the test schemes over `T.left`, are identified with
the points of a scheme `W` over `T.left`, then `W` is the fibre product `H ×_Y T.left`. -/
theorem isPullback_pointsIsoToHom :
    IsPullback (pointsIsoToHom φ) (yoneda.map w) p T.hom.hom := by
  refine IsPullback.of_forall_isPullback_app fun ⟨V⟩ => ?_
  rw [Types.isPullback_iff]
  have hid (f : V ⟶ T.left) : T.hom.hom.app (op V) (𝟙 V ≫ f) = T.hom.hom.app (op V) f := by
    rw [Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · ext (t : V ⟶ W)
    exact (φ.hom.app (op (composedTest T w t)) (composedTestPoint T w t)).2.app.trans (hid _)
  · rintro (t₁ : V ⟶ W) (t₂ : V ⟶ W) ⟨h₁, h₂⟩
    have ht₂ : (yoneda.map w).app (op V) t₂ = testPoint (mapTest (t₂ ≫ w)) :=
      (yonedaEquiv_yoneda_map (t₂ ≫ w)).symm
    have ht₁ : (yoneda.map w).app (op V) t₁ = testPoint (mapTest (t₂ ≫ w)) := h₂.trans ht₂
    rw [pointsIsoToHom_app_eq φ (t₂ ≫ w) t₁ ht₁, pointsIsoToHom_app_eq φ (t₂ ≫ w) t₂ ht₂] at h₁
    exact congrArg Subtype.val
      ((φ.app (op (mapTest (t₂ ≫ w)))).toEquiv.injective (OverPresheafAux.OverArrows.ext h₁))
  · rintro (x : H.obj (op V)) (s : V ⟶ T.left) hx
    have hx' : p.app (op V) x = yonedaEquiv (yoneda.map s ≫ T.hom.hom) := hx.trans (hid s).symm
    let y : ((CostructuredArrow.map T.hom).op ⋙ presheafPointsOver p).obj (op (mapTest s)) :=
      ⟨x, ⟨hx'⟩⟩
    refine ⟨((φ.app (op (mapTest s))).toEquiv.symm y).1, ?_, ?_⟩
    · rw [pointsIsoToHom_app_eq φ s _ ((φ.app (op (mapTest s))).toEquiv.symm y).2]
      exact congrArg Subtype.val ((φ.app (op (mapTest s))).toEquiv.apply_symm_apply y)
    · exact ((φ.app (op (mapTest s))).toEquiv.symm y).2.trans (yonedaEquiv_yoneda_map s)

end Pullback

section Sheaf

variable {Y : AlgebraicSpaces B S hS}

/-- The test scheme over `Y` given by a section `y` of `Y` over `V`. -/
def testOf (V : BigFppfOver B S hS) (y : Y.1.obj (op V)) : SchemesOver Y :=
  CostructuredArrow.mk (Y := V)
    (ObjectProperty.homMk (yonedaEquiv.symm y) : (schemeSpaceFunctor B S hS).obj V ⟶ Y)

/-- The point of `Y` at the test scheme `testOf V y` is `y`. -/
theorem testPoint_testOf (V : BigFppfOver B S hS) (y : Y.1.obj (op V)) :
    testPoint (testOf V y) = y :=
  yonedaEquiv.apply_symm_apply y

/-- The lift of a morphism `g : V ⟶ T.left` of the big fppf site to a morphism of test schemes
over `Y` into `T`. -/
abbrev liftTestAlong (T : SchemesOver Y) {V : BigFppfOver B S hS} (g : V ⟶ T.left) :
    CostructuredArrow.mk (Y := V) ((schemeSpaceFunctor B S hS).map g ≫ T.hom) ⟶ T :=
  CostructuredArrow.homMk g rfl

/-- Pushing a presieve forward along a composite of functors is pushing it forward twice. -/
theorem _root_.CategoryTheory.Presieve.map_comp_functor {C D E : Type*} [Category* C]
    [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm (fun _ _ ⟨h⟩ => Presieve.map_map (Presieve.map_map h)) ?_
  rintro _ _ ⟨⟨h⟩⟩
  exact Presieve.map_map (F := F ⋙ G) h

/-- Every morphism into the underlying object of a test scheme lifts, so pulling a presieve back
to the test schemes and pushing it forward again returns it. -/
theorem map_functorPullback_testProj (T : SchemesOver Y) (P : Presieve T.left) :
    (P.functorPullback (SchemesOver.proj Y)).map (SchemesOver.proj Y) = P := by
  refine le_antisymm (fun _ _ ⟨hg⟩ => hg) (fun V g hg => ?_)
  exact Presieve.map_map (F := SchemesOver.proj Y) (f := liftTestAlong T g) hg

/-- **A family of the big fppf site whose underlying schemes form an fpqc covering lifts to a
covering sieve of the test schemes over `Y`.** -/
theorem generate_functorPullback_mem_fpqcTopology (T : SchemesOver Y) {P : Presieve T.left}
    (hP : P ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)) T.left) :
    (Sieve.generate P).functorPullback (SchemesOver.proj Y) ∈ fpqcTopology Y T := by
  refine (fpqcTopology Y).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (R := P.functorPullback (SchemesOver.proj Y)) ?_)
  · rintro V g ⟨W, h, k, hk, rfl⟩
    exact ⟨_, h.left, (SchemesOver.proj Y).map k, hk, rfl⟩
  · rw [Precoverage.mem_comap_iff] at hP ⊢
    have h := Presieve.map_comp_functor (SchemesOver.proj Y) (BigFppfOver.toScheme B S hS)
      (P.functorPullback (SchemesOver.proj Y))
    rw [map_functorPullback_testProj] at h
    exact h ▸ hP

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme in
/-- Fibre products of the big fppf site over `S`. -/
private theorem hasPullbacks_bigFppfOver' : HasPullbacks (BigFppfOver B S hS) :=
  let := B.hasPullbacks_schemes
  inferInstance

attribute [local instance] hasPullbacks_bigFppfOver' preservesLimitsOfShape_walkingCospan_toScheme

/-- **The projection from the test schemes over `Y` to the big fppf site is cocontinuous** for
the fpqc topologies. -/
theorem testProj_cocontinuous_fpqc {T : SchemesOver Y} {S' : Sieve T.left}
    (hS' : S' ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck T.left) :
    S'.functorPullback (SchemesOver.proj Y) ∈ fpqcTopology Y T := by
  suffices H : ∀ (V : BigFppfOver B S hS) (R : Sieve V),
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).Saturate V R →
      ∀ (X : SchemesOver Y) (g : X.left ⟶ V),
        (R.pullback g).functorPullback (SchemesOver.proj Y) ∈ fpqcTopology Y X by
    simpa using H _ S' hS' T (𝟙 _)
  intro V R hR
  induction hR with
  | of V P hP =>
    intro X g
    rw [← Sieve.pullbackArrows_comm]
    exact generate_functorPullback_mem_fpqcTopology X (Precoverage.pullbackArrows_mem g hP)
  | top V =>
    intro X g
    simp only [Sieve.pullback_top]
    exact (fpqcTopology Y).top_mem _
  | pullback V R hR W f ih =>
    intro X g
    rw [← Sieve.pullback_comp]
    exact ih X (g ≫ f)
  | transitive V R R' hR hR' ih1 ih2 =>
    intro X g
    refine (fpqcTopology Y).transitive (ih1 X g) _ fun X' k hk => ?_
    convert ih2 (f := (SchemesOver.proj Y).map k ≫ g) hk X' (𝟙 _) using 1
    ext X'' m
    simp [Sieve.functorPullback]

/-- The projection from the test schemes over `Y` to the big fppf site carries covering sieves of
the big fppf topology back to covering sieves of the fpqc topology on the test schemes. -/
theorem functorPullback_testProj_mem_fpqcTopology {T : SchemesOver Y} {S' : Sieve T.left}
    (hS' : S' ∈ BigFppfOver.topology B S hS T.left) :
    S'.functorPullback (SchemesOver.proj Y) ∈ fpqcTopology Y T :=
  testProj_cocontinuous_fpqc ((show BigFppfOver.topology B S hS ≤
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck from
    BigFppfSite.topology_over_le_fpqcPrecoverage_comap_toGrothendieck B (B.obj hS)) _ hS')

/-- **A presheaf over `Y` whose points over `Y` form an fpqc sheaf on the test schemes over `Y`
is an fppf sheaf.** -/
theorem isSheaf_of_isSheaf_presheafPointsOver {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : H ⟶ Y.1) (hR : Presheaf.IsSheaf (fpqcTopology Y) (presheafPointsOver p)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) H := by
  rw [isSheaf_iff_isSheaf_of_type] at hR ⊢
  have hY := (isSheaf_iff_isSheaf_of_type _ _).1 Y.2.isSheaf
  intro T R0 hR0 x hx
  let yfam : Presieve.FamilyOfElements Y.1 R0.arrows := fun V f hf => p.app (op V) (x f hf)
  have hyc : yfam.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc
    simp only [yfam]
    rw [← NatTrans.naturality_apply p g₁.op, ← NatTrans.naturality_apply p g₂.op,
      hx g₁ g₂ h₁ h₂ hc]
  obtain ⟨y, hy, hyu⟩ := hY R0 hR0 yfam hyc
  let T' : SchemesOver Y := testOf T y
  have hpt : ∀ {Z : SchemesOver Y} (h : Z ⟶ T') (hh : R0 h.left),
      p.app (op Z.left) (x h.left hh) = testPoint Z := by
    intro Z h hh
    refine (hy h.left hh).symm.trans ?_
    rw [← testPoint_naturality h]
    exact congrArg _ (testPoint_testOf T y).symm
  let z : Presieve.FamilyOfElements (presheafPointsOver p)
      (Sieve.functorPullback (X := T') (SchemesOver.proj Y) R0).arrows :=
    fun Z h hh => ⟨x h.left hh, ⟨hpt h hh⟩⟩
  have hz : z.Compatible := fun Z₁ Z₂ W g₁ g₂ h₁ h₂ hh₁ hh₂ hc =>
    OverPresheafAux.OverArrows.ext (hx g₁.left g₂.left hh₁ hh₂ (congrArg CommaMorphism.left hc))
  obtain ⟨t, ht, htu⟩ := hR _ (functorPullback_testProj_mem_fpqcTopology (T := T') hR0) z hz
  refine ⟨t.1, fun V f hf => congrArg Subtype.val (ht (liftTestAlong T' f) hf), fun t' ht' => ?_⟩
  have hpt' : p.app (op T) t' = y := by
    refine hyu (p.app (op T) t') fun V f hf => ?_
    rw [← NatTrans.naturality_apply p f.op, ht' f hf]
  exact congrArg Subtype.val (htu (⟨t', ⟨hpt'.trans (testPoint_testOf T y).symm⟩⟩ :
    (presheafPointsOver p).obj (op T'))
    fun Z h hh => OverPresheafAux.OverArrows.ext (ht' h.left hh))

end Sheaf

end AlgebraicGeometry.Space
