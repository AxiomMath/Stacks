module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Functor.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProper
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.OpenImmersion

/-!
# Proper-support direct image through a compactification

Let `j : X ⟶ X̄` be an open immersion in a big étale site and let `f̄ : X̄ ⟶ Y` be proper.
Extension by zero does not change the proper-support direct image of an abelian sheaf on the
small étale site: there is a canonical map `f_! F ⟶ f̄_! (j_! F)` for `f = j ≫ f̄`, and it is an
isomorphism. Since `f̄` is proper, `f̄_!` agrees with ordinary direct image, so the same map
identifies `f_! F` with `f̄_* (j_! F)`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compactificationFShriekMap` — the canonical comparison from
  `f_! F` to the proper-support direct image of the extension by zero, bundled with the
  factorisation through the extension-by-zero unit that characterises it.

## Main results

* `AlgebraicGeometry.SmallEtale.openRestrictionIso_app_apply` — the identification of restriction
  along an open immersion with direct image along post-composition, evaluated on a section over
  an object of the smaller site: it is the base-change unit followed by restriction along the
  graph.
* `AlgebraicGeometry.SmallEtale.compactificationFShriekMap_isIso` — the comparison is an
  isomorphism.
* `AlgebraicGeometry.SmallEtale.compactificationFShriekMap_to_pushforward_isIso` — composed with
  the inclusion into ordinary direct image it is still an isomorphism, so
  `f̄_* ∘ j_! = f_!`.
* `AlgebraicGeometry.SmallEtale.compactificationFShriekMap_naturality` — the comparison is
  natural in the abelian sheaf, hence an identification of the two direct-image functors.

## Implementation notes

The open subscheme is presented as an object `U` of the small étale site of the compactification,
and restriction along it is available in two forms: direct image along post-composition with `U`,
which is `AlgebraicGeometry.abelianRestriction`, and inverse image along small étale base change.
`AlgebraicGeometry.SmallEtale.openRestrictionIso` identifies them; what the comparison needs is
the value of that identification on a section, which
`AlgebraicGeometry.SmallEtale.openRestrictionIso_app_apply` computes from the unit of the
base-change adjunction and the graph `AlgebraicGeometry.smallEtaleGraph`. The bridge between the
two descriptions of the graph is
`AlgebraicGeometry.SmallEtale.openPostcomposeAdjunction_unit_app`, proved from the triangle
identity rather than by unfolding the restricted adjunction.

The unit of the extension-by-zero adjunction identifies `F` with the restriction of `j_! F`, so
the comparison is that identification on proper-support images followed by the open-inclusion
comparison `AlgebraicGeometry.SmallEtale.openInclusionShriekMap`. Invertibility is a diagram
chase: composing proper-support direct images identifies `f̄_!(j_! F)` with `f_! F` once the
extension by zero `j_! F` is identified with the proper-support subsheaf `j_! F` of the direct
image, which is the content of
`AlgebraicGeometry.SmallEtale.abelianExtensionByZeroToPushforward_range_eq_fShriekSubsheaf`;
the graph restriction formula then identifies the resulting isomorphism with the canonical
comparison. The three purely diagrammatic steps of that chase are isolated as
`eq_of_retraction_naturality`, `map_comp_paste` and `isIso_of_comparison_diagram`.

## References

* [Stacks Project, Tag 0F52](https://stacks.math.columbia.edu/tag/0F52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

/-! ### Restriction along an open immersion, evaluated on a section -/

/-- Restricting a section along `g.op` and then along `f.op` is the identity when `f ≫ g = 𝟙`. -/
private theorem map_op_map_op_apply_of_comp_eq_id {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (s : P.obj (op X)) : P.map f.op (P.map g.op s) = s := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, h, op_id]
  simp

section OpenRestriction

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

/-- The unit of the adjunction between post-composition with an open immersion and base change
along it is a section of the first projection of the fibre product. -/
public theorem openPostcomposeAdjunction_unit_left_fst (W : SmallEtale B X'.obj X'.property) :
    ((openPostcomposeAdjunction B j).unit.app W).hom.left ≫
      pullback.fst ((openPostcompose B j).obj W).obj.hom j = 𝟙 W.obj.left := by
  have := hasPullbacks_bigEtaleSite B
  have h := congrArg (SmallEtale.toScheme B X.obj X.property).map
    ((openPostcomposeAdjunction B j).left_triangle_components W)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    openPostcompose_toScheme_map, openPostcomposeAdjunction_counit_toScheme] at h
  exact B.inclusion.map_injective h

/-- The unit of the adjunction between post-composition with an open immersion and base change
along it is the graph `AlgebraicGeometry.smallEtaleGraph` of the test object. -/
public theorem openPostcomposeAdjunction_unit_app (W : SmallEtale B X'.obj X'.property) :
    (openPostcomposeAdjunction B j).unit.app W =
      smallEtaleGraph B X.obj X.property (openSiteObject B j) W := by
  have := hasPullbacks_bigEtaleSite B
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (f := ((openPostcompose B j).obj W).obj.hom) (g := j)
  · refine (openPostcomposeAdjunction_unit_left_fst B j W).trans ?_
    symm
    simp only [smallEtaleGraph, Over.mapPullbackAdj, Adjunction.mk', Adjunction.mkOfHomEquiv]
    exact pullback.lift_fst _ _ _
  · exact (Over.w _).trans (Over.w _).symm

variable (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

private theorem openRestrictionIso_app_apply_unit (W : SmallEtale B X'.obj X'.property)
    (s : H.obj.obj (op ((openPostcompose B j).obj W))) :
    ((openRestrictionIso.{u, v} B j).hom.app H).hom.app (op W) s =
      ((openRestriction.{u, v} B j).obj H).obj.map
          ((openPostcomposeAdjunction B j).unit.app W).op
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app
            (op ((openPostcompose B j).obj W)) s) := by
  set c := (openPostcomposeAdjunction B j).unit.app W with hc
  set k := (openPostcomposeAdjunction B j).counit.app ((openPostcompose B j).obj W) with hk
  have htri : (openPostcompose B j).map c ≫ k = 𝟙 _ :=
    (openPostcomposeAdjunction B j).left_triangle_components W
  have hnat : ((openRestrictionIso.{u, v} B j).hom.app H).hom.app (op W)
        (H.obj.map ((openPostcompose B j).map c).op (H.obj.map k.op s)) =
      ((openRestriction.{u, v} B j).obj H).obj.map c.op
        (((openRestrictionIso.{u, v} B j).hom.app H).hom.app
          (op ((smallEtaleBaseChange B j).obj ((openPostcompose B j).obj W)))
            (H.obj.map k.op s)) :=
    ConcreteCategory.congr_hom
      (((openRestrictionIso.{u, v} B j).hom.app H).hom.naturality c.op) _
  have hid := map_op_map_op_apply_of_comp_eq_id.{max (u + 1) v} H.obj _ _ htri s
  rwa [hid, openRestrictionIso_unit_app.{u, v} B j H ((openPostcompose B j).obj W) s] at hnat

private theorem openRestrictionIso_app_apply_graph (W : SmallEtale B X'.obj X'.property)
    (s : H.obj.obj (op ((openPostcompose B j).obj W))) :
    ((openRestrictionIso.{u, v} B j).hom.app H).hom.app (op W) s =
      ((openRestriction.{u, v} B j).obj H).obj.map
          (smallEtaleGraph B X.obj X.property (openSiteObject B j) W).op
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app H).hom.app
            (op ((openPostcompose B j).obj W)) s) := by
  rw [← openPostcomposeAdjunction_unit_app B j W]
  exact openRestrictionIso_app_apply_unit B j H W s

end OpenRestriction

section OpenRestrictionObject

variable (B : BigEtaleSite.{u}) {X : B.Scheme} (U : SmallEtale B X.obj X.property)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  (H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (W : SmallEtale B U.obj.left.obj U.obj.left.property)

/-- The identification of restriction along an open immersion with direct image along
post-composition, evaluated on a section of `H` over the image of an object `W` of the small
étale site of the open subscheme: it is the unit of the base-change adjunction followed by
restriction along the graph `AlgebraicGeometry.smallEtaleGraph` of `W`. -/
public theorem openRestrictionIso_app_apply
    (s : H.obj.obj (op ((smallEtalePostcompose B X.obj X.property U).obj W))) :
    ((openRestrictionIso.{u, v} B U.obj.hom).hom.app H).hom.app (op W) s =
      (((smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).obj H).obj.map
          (smallEtaleGraph B X.obj X.property U W).op
        ((((smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).unit.app H).hom.app
            (op ((smallEtalePostcompose B X.obj X.property U).obj W)) s) :=
  openRestrictionIso_app_apply_graph.{u, v} B U.obj.hom H W s

/-- For an open immersion the graph `AlgebraicGeometry.smallEtaleGraph` of an object of the
smaller site is an isomorphism: post-composition with an open immersion is fully faithful, so
the unit of its adjunction with base change is invertible. -/
public theorem isIso_smallEtaleGraph :
    IsIso (smallEtaleGraph B X.obj X.property U W) := by
  have h : IsIso ((openPostcomposeAdjunction B U.obj.hom).unit.app W) := inferInstance
  exact openPostcomposeAdjunction_unit_app B U.obj.hom W ▸ h

/-- `AlgebraicGeometry.SmallEtale.openRestrictionIso_app_apply` as an equality of group
homomorphisms. -/
public theorem openRestrictionIso_hom_app_app :
    ((openRestrictionIso.{u, v} B U.obj.hom).hom.app H).hom.app (op W) =
      (((smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous
          AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).unit.app H).hom.app
            (op ((smallEtalePostcompose B X.obj X.property U).obj W)) ≫
        (((smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).obj H).obj.map
          (smallEtaleGraph B X.obj X.property U W).op := by
  ext s
  exact openRestrictionIso_app_apply.{u, v} B U H W s

end OpenRestrictionObject

/-! ### Subsheaves with the same sections -/

section Subsheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {F G H : Sheaf J AddCommGrpCat.{v}}

/-- A morphism of abelian sheaves whose image is sectionwise contained in the image of a
sectionwise injective morphism factors through it. -/
private theorem exists_sheafLift_of_range_subset (f : F ⟶ H) (g : G ⟶ H)
    (hg : ∀ V, Function.Injective (g.hom.app V))
    (h : ∀ V, Set.range (f.hom.app V) ⊆ Set.range (g.hom.app V)) :
    ∃ l : F ⟶ G, l ≫ g = f := by
  classical
  choose a ha using fun V s => h V ⟨s, rfl⟩
  let l : F ⟶ G := ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun := a V
      map_zero' := hg V (by simp [ha])
      map_add' := fun x y => hg V (by simp [ha]) }
    naturality V W k := by
      ext x
      apply hg W
      symm
      show (g.hom.app W) (G.obj.map k (a V x)) = (g.hom.app W) (a W (F.obj.map k x))
      rw [← ConcreteCategory.comp_apply, g.hom.naturality]
      show H.obj.map k (g.hom.app V (a V x)) = _
      rw [ha, ha]
      exact (ConcreteCategory.congr_hom (f.hom.naturality k) x).symm }⟩
  exact ⟨l, by ext V x; exact ha V x⟩

/-- Two subsheaves of an abelian sheaf with the same sections are isomorphic over it. -/
private theorem exists_sheafIso_of_range_eq (f : F ⟶ H) (g : G ⟶ H) [Mono f] [Mono g]
    (h : ∀ V, Set.range (f.hom.app V) = Set.range (g.hom.app V)) :
    ∃ e : F ≅ G, e.hom ≫ g = f := by
  have inj {A : Sheaf J AddCommGrpCat.{v}} (m : A ⟶ H) [Mono m] (V) :
      Function.Injective (m.hom.app V) := by
    have : Mono m.hom := (sheafToPresheaf J AddCommGrpCat.{v}).map_mono m
    exact (AddCommGrpCat.mono_iff_injective (m.hom.app V)).mp inferInstance
  obtain ⟨a, ha⟩ := exists_sheafLift_of_range_subset f g (inj g) (fun V => (h V).le)
  obtain ⟨b, hb⟩ := exists_sheafLift_of_range_subset g f (inj f) (fun V => (h V).ge)
  exact ⟨⟨a, b, (cancel_mono f).mp (by simp [Category.assoc, hb, ha]),
    (cancel_mono g).mp (by simp [Category.assoc, ha, hb])⟩, ha⟩

end Subsheaf

/-! ### Three diagram lemmas -/

section Diagrams

variable {C : Type*} [Category C]

/-- If `a ≫ b` is a section of `g` and `k` is a monomorphism under which `e` and `h` both
restrict to the same map out of the source of `a`, then `a ≫ b ≫ e = a ≫ h`. -/
private theorem eq_of_retraction_naturality {A M D E K : C}
    (a : A ⟶ M) (b : M ⟶ D) (g : D ⟶ A) (e : D ⟶ E) (k : E ⟶ K) [Mono k] (l : A ⟶ K)
    (h : M ⟶ E) (t : M ⟶ K)
    (habg : a ≫ b ≫ g = 𝟙 A) (hek : e ≫ k = g ≫ l) (ht : t = h ≫ k) (hl : l = a ≫ t) :
    a ≫ b ≫ e = a ≫ h := by
  apply (cancel_mono k).mp
  simp only [Category.assoc]
  rw [hek, ← Category.assoc b, ← Category.assoc a, habg, Category.id_comp, hl, ht]

/-- Pasting two squares over a functor along a factorisation `q ≫ j = n` of an arrow. -/
private theorem map_comp_paste {D : Type*} [Category D] (Φ : C ⥤ D)
    {P Q R : C} {S T V A : D}
    (q : P ⟶ Q) (j : Q ⟶ R) (n : P ⟶ R)
    (a : S ⟶ T) (b : T ⟶ V) (p : S ⟶ Φ.obj P)
    (p' : T ⟶ Φ.obj Q) (s : V ⟶ A) (d : Φ.obj R ⟶ A)
    (ha : a ≫ p' = p ≫ Φ.map q) (hb : b ≫ s = p' ≫ Φ.map j ≫ d) (hq : q ≫ j = n) :
    (a ≫ b) ≫ s = p ≫ Φ.map n ≫ d := by
  rw [Category.assoc, hb, ← Category.assoc, ha]
  simp only [Category.assoc, ← Φ.map_comp_assoc, hq]

/-- A comparison arrow `α` which, after two monomorphisms, agrees with the inverse of a given
isomorphism `r` is itself an isomorphism. -/
private theorem isIso_of_comparison_diagram {S T J A A' M M' K : C}
    (r : T ≅ S) (s : S ⟶ A) [Mono s] (t : T ⟶ K)
    (n : K ⟶ M) (d : M ⟶ A) (u : K ⟶ M') (d' : M' ⟶ A')
    (e : A ⟶ A') [Mono e] (ne : M ⟶ M')
    (α : S ⟶ T) (i : S ⟶ J) (o : J ⟶ T) (p : J ⟶ A')
    (hr : r.hom ≫ s = t ≫ n ≫ d) (hn : n ≫ ne = u)
    (hd : d ≫ e = ne ≫ d') (ho : o ≫ t ≫ u ≫ d' = p)
    (hi : i ≫ p = s ≫ e) (hα : α = i ≫ o) : IsIso α := by
  have h : α ≫ r.hom = 𝟙 _ := by
    apply (cancel_mono s).mp
    apply (cancel_mono e).mp
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc r.hom, hr]
    simp only [Category.assoc]
    rw [hd, ← Category.assoc n, hn, hα]
    simp only [Category.assoc]
    rw [ho, hi]
  obtain rfl : α = r.inv := (cancel_mono r.hom).mp (by simpa using h)
  infer_instance

end Diagrams

/-! ### The canonical comparison -/

section Compactification

variable (B : BigEtaleSite.{u}) {Xbar Y : B.Scheme} (fbar : Xbar ⟶ Y)
  [IsProper (B.inclusion.map fbar)] (U : SmallEtale B Xbar.obj Xbar.property)
  [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) AddCommGrpCat.{u + 1})

/-- **Stacks 0F52.** The canonical map `f_! F ⟶ f̄_!(j_! F)` for an open immersion `j : X ⟶ X̄`
with `f = j ≫ f̄`: the extension-by-zero unit, which identifies `F` with the restriction of
`j_! F`, followed by the open-inclusion comparison of Stacks 0F53. The subtype records that
factorisation, which is what pins the map down. -/
@[stacks 0F52 "canonical comparison"]
public noncomputable def compactificationFShriekMap :
    letI : IsSeparated (B.inclusion.map fbar) := inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar)) := by
      change LocallyOfFiniteType (B.inclusion.map U.obj.hom ≫ B.inclusion.map fbar)
      infer_instance
    let Fbar := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
    let pull := (smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Xbar.obj Xbar.property)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    let push := (smallEtaleBaseChange B (U.obj.hom ≫ fbar)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    let Gsrc := (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val
    let Gpull := (fShriekSubsheaf B (U.obj.hom ≫ fbar) (pull.obj Fbar)).val
    let Gtgt := (fShriekSubsheaf B fbar Fbar).val
    {α : Gsrc.obj.left ⟶ Gtgt.obj.left //
      ∃ i : Gsrc.obj.left ≅ Gpull.obj.left,
        let unit := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
        let e := unit ≫ (openRestrictionIso.{u, u} B U.obj.hom).hom.app Fbar
        (i.hom ≫ Gpull.arrow = Gsrc.arrow ≫ push.map e) ∧
        (α = i.hom ≫ (openInclusionShriekMap B U.obj.hom fbar Fbar).val)} := by
  classical
  letI : IsSeparated (B.inclusion.map fbar) := inferInstance
  letI : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
  letI : LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar)) := by
    change LocallyOfFiniteType (B.inclusion.map U.obj.hom ≫ B.inclusion.map fbar)
    infer_instance
  let Fbar := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
  let pull := (smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let Gsrc := (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val
  let Gpull := (fShriekSubsheaf B (U.obj.hom ≫ fbar) (pull.obj Fbar)).val
  let unit := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
  let e := unit ≫ (openRestrictionIso.{u, u} B U.obj.hom).hom.app Fbar
  letI : IsIso unit :=
    abelianExtensionByZeroAdjunction_unit_isIso B Xbar.obj Xbar.property U F
  let eIso : F ≅ (openRestriction.{u, u} B U.obj.hom).obj Fbar :=
    asIso unit ≪≫ (openRestrictionIso.{u, u} B U.obj.hom).app Fbar
  letI : IsIso e := (inferInstance : IsIso eIso.hom)
  let phi := fShriekMap B (U.obj.hom ≫ fbar) F (pull.obj Fbar) e
  letI : IsIso phi.val := by
    let m := phi.val
    let n := (fShriekMap B (U.obj.hom ≫ fbar) (pull.obj Fbar) F (inv e)).val
    have hmn : m ≫ n = 𝟙 _ := by
      rw [← fShriekMap_comp]
      have h : e ≫ inv e = 𝟙 F := by simp
      rw [h, fShriekMap_id]
    have hnm : n ≫ m = 𝟙 _ := by
      rw [← fShriekMap_comp]
      have h : inv e ≫ e = 𝟙 (pull.obj Fbar) := by
        simp [pull]
      rw [h, fShriekMap_id]
    exact ⟨⟨n, hmn, hnm⟩⟩
  let i : Gsrc.obj.left ≅ Gpull.obj.left := asIso phi.val
  exact ⟨i.hom ≫ (openInclusionShriekMap B U.obj.hom fbar Fbar).val, ⟨i, phi.property, rfl⟩⟩

/-- Composing the canonical map from extension by zero to the direct image with the
identification of `F` with the restriction of `j_! F` gives the unit of the base-change
adjunction. -/
private theorem extensionByZeroToPushforward_comp_unit :
    let H := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
    let base := smallEtaleBaseChange B U.obj.hom
    let adj := base.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Xbar.obj Xbar.property)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    let e := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F ≫
      (openRestrictionIso.{u, u} B U.obj.hom).hom.app H
    (abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F ≫
      (base.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Xbar.obj Xbar.property)
        (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).map e = adj.unit.app H := by
  intro H base adj e
  let extAdj := abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U
  let post := smallEtalePostcompose B Xbar.obj Xbar.property U
  let n := (abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F
  apply (extAdj.homEquiv F _).injective
  simp only [Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  let graph := smallEtaleGraph B Xbar.obj Xbar.property U W.unop
  have : IsIso graph := isIso_smallEtaleGraph B U W.unop
  have hres : (extAdj.unit.app F).hom.app W ≫
      n.hom.app (op (post.obj W.unop)) ≫ F.obj.map graph.op = 𝟙 _ := by
    ext s
    exact abelianExtensionByZeroToPushforward_graph B Xbar.obj Xbar.property U F W.unop s
  exact eq_of_retraction_naturality
    ((extAdj.unit.app F).hom.app W)
    (n.hom.app (op (post.obj W.unop)))
    (F.obj.map graph.op)
    (e.hom.app (op (base.obj (post.obj W.unop))))
    (((base.sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Xbar.obj Xbar.property)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).obj H).obj.map graph.op)
    (e.hom.app W)
    ((adj.unit.app H).hom.app (op (post.obj W.unop)))
    (((openRestrictionIso.{u, u} B U.obj.hom).hom.app H).hom.app W)
    hres (e.hom.naturality graph.op).symm
    (openRestrictionIso_hom_app_app.{u, u} B U H W.unop) rfl

/-- The open-inclusion comparison, followed by the inclusion into ordinary direct image and the
unit of the base-change adjunction, is the inclusion of the proper-support direct image along the
composite. -/
private theorem openInclusionShriekMap_comp_unit {X' X : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)] [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let adj := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
    let pull := (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
    let push := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    let d := Functor.sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_compIso B X' X Y j f).val
      AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X'.obj X'.property)
    (openInclusionShriekMap B j f G).val ≫ (fShriekSubsheaf B f G).val.arrow ≫
      push.map (adj.unit.app G) ≫ (d.app (pull.obj G)).hom =
      (fShriekSubsheaf B (j ≫ f) (pull.obj G)).val.arrow := by
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    show LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  intro adj pull push d
  ext V a
  have h := ((openInclusionShriekMap B j f G).property.2 V.unop a).1
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  show (pull.obj G).obj.map (e.inv.app V.unop).op
    ((adj.unit.app G).hom.app (op ((smallEtaleBaseChange B f).obj V.unop))
      ((fShriekSubsheaf B f G).val.arrow.hom.app V
        ((openInclusionShriekMap B j f G).val.hom.app V a))) = _
  rw [← h]
  exact map_op_map_op_apply_of_comp_eq_id (pull.obj G).obj _ _ (e.inv_hom_id_app V.unop) _

/-- Extension by zero along an open immersion is the proper-support direct image: the canonical
map to the direct image has the same sections as the proper-support subsheaf, hence identifies
the two. -/
private theorem exists_abelianExtensionByZero_iso_fShriekSubsheaf :
    ∃ q : (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F ≅
        (fShriekSubsheaf B U.obj.hom F).val.obj.left,
      q.hom ≫ (fShriekSubsheaf B U.obj.hom F).val.arrow =
        (abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F := by
  have : Mono ((abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F) :=
    abelianExtensionByZeroToPushforward_mono B Xbar.obj Xbar.property U F
  exact exists_sheafIso_of_range_eq _ _ (fun V =>
    abelianExtensionByZeroToPushforward_range_eq_fShriekSubsheaf
      B Xbar.obj Xbar.property U F V.unop)

/-- Composing proper-support direct images identifies `f̄_!(j_! F)` with `f_! F` as subsheaves of
the direct image along `j ≫ f̄`, once extension by zero is identified with the proper-support
subsheaf of `j_* F`. -/
private theorem exists_compactificationCompIso
    [LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar))] :
    ∃ r : (fShriekSubsheaf B fbar
          ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F)).val.obj.left ≅
        (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val.obj.left,
      r.hom ≫ (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val.arrow =
        (fShriekSubsheaf B fbar
            ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F)).val.arrow ≫
          ((smallEtaleBaseChange B fbar).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (SmallEtale.topology B Y.obj Y.property)
              (SmallEtale.topology B Xbar.obj Xbar.property)).map
            ((abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F) ≫
          ((Functor.sheafPushforwardContinuousComp'
            (smallEtaleBaseChange_compIso B U.obj.left Xbar Y U.obj.hom fbar).val
            AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B Xbar.obj Xbar.property)
            (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).app F).hom := by
  let Fbar := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
  let Gsrc := (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val
  let Gtgt := (fShriekSubsheaf B fbar Fbar).val
  let Gj := (fShriekSubsheaf B U.obj.hom F).val
  let Giter := (fShriekSubsheaf B fbar Gj.obj.left).val
  let pushbar := (smallEtaleBaseChange B fbar).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)
  let n := (abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F
  let d := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B U.obj.left Xbar Y U.obj.hom fbar).val
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  obtain ⟨q, hq⟩ := exists_abelianExtensionByZero_iso_fShriekSubsheaf B U F
  let q' := (properSupportFunctor B fbar).mapIso q
  let k := (properSupportSheaf_compIso B U.obj.hom fbar F).val
  have hq' : q'.hom ≫ Giter.arrow = Gtgt.arrow ≫ pushbar.map q.hom :=
    (fShriekMap B fbar Fbar Gj.obj.left q.hom).property
  have hk : k.hom ≫ Gsrc.arrow = Giter.arrow ≫ pushbar.map Gj.arrow ≫ (d.app F).hom :=
    (properSupportSheaf_compIso B U.obj.hom fbar F).property
  exact ⟨q' ≪≫ k, map_comp_paste pushbar q.hom Gj.arrow n q'.hom k.hom Gtgt.arrow
    Giter.arrow Gsrc.arrow (d.app F).hom hq' hk hq⟩

/-- **Stacks 0F52.** The canonical compactification comparison is an isomorphism. -/
@[stacks 0F52 "isomorphism"]
public theorem compactificationFShriekMap_isIso :
    IsIso (compactificationFShriekMap B fbar U F).val := by
  let : IsSeparated (B.inclusion.map fbar) := inferInstance
  let : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
  let : LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar)) := by
    show LocallyOfFiniteType (B.inclusion.map U.obj.hom ≫ B.inclusion.map fbar)
    infer_instance
  classical
  let ext := abelianExtensionByZero B Xbar.obj Xbar.property U
  let Fbar := ext.obj F
  let Gsrc := (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val
  let Gtgt := (fShriekSubsheaf B fbar Fbar).val
  let pushbar := (smallEtaleBaseChange B fbar).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)
  let push := (smallEtaleBaseChange B (U.obj.hom ≫ fbar)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let pushj := (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let pull := (smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let adj := (smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let n := (abelianExtensionByZeroToPushforward B Xbar.obj Xbar.property U).app F
  let d := Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B U.obj.left Xbar Y U.obj.hom fbar).val
    AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  have hcomp := exists_compactificationCompIso B fbar U F
  obtain ⟨r, hr⟩ := hcomp
  let unit := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
  let e := unit ≫ (openRestrictionIso.{u, u} B U.obj.hom).hom.app Fbar
  have : IsIso unit := abelianExtensionByZeroAdjunction_unit_isIso B Xbar.obj Xbar.property U F
  let eIso : F ≅ (openRestriction.{u, u} B U.obj.hom).obj Fbar :=
    asIso unit ≪≫ (openRestrictionIso.{u, u} B U.obj.hom).app Fbar
  have : IsIso e := (inferInstance : IsIso eIso.hom)
  have hn : n ≫ pushj.map e = adj.unit.app Fbar :=
    extensionByZeroToPushforward_comp_unit B U F
  have hprop := (compactificationFShriekMap B fbar U F).property
  obtain ⟨i, hi, halpha⟩ := hprop
  let Gpull := (fShriekSubsheaf B (U.obj.hom ≫ fbar) (pull.obj Fbar)).val
  let o := (openInclusionShriekMap B U.obj.hom fbar Fbar).val
  have ho : o ≫ Gtgt.arrow ≫ pushbar.map (adj.unit.app Fbar) ≫
      (d.app (pull.obj Fbar)).hom = Gpull.arrow :=
    openInclusionShriekMap_comp_unit B U.obj.hom fbar Fbar
  exact isIso_of_comparison_diagram r Gsrc.arrow Gtgt.arrow
    (pushbar.map n) (d.app F).hom (pushbar.map (adj.unit.app Fbar))
    (d.app (pull.obj Fbar)).hom (push.map e) (pushbar.map (pushj.map e))
    (compactificationFShriekMap B fbar U F).val i.hom o Gpull.arrow
    hr ((pushbar.map_comp n (pushj.map e)).symm.trans (congrArg pushbar.map hn))
    (d.hom.naturality e).symm ho hi halpha

/-- **Stacks 0F52.** Since the compactification is proper, the same canonical map identifies
`f_! F` with the ordinary direct image `f̄_*(j_! F)`. -/
@[stacks 0F52 "ordinary direct image"]
public theorem compactificationFShriekMap_to_pushforward_isIso :
    letI : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
    let Fbar := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
    IsIso ((compactificationFShriekMap B fbar U F).val ≫
      (fShriekSubsheaf B fbar Fbar).val.arrow) := by
  let Fbar := (abelianExtensionByZero B Xbar.obj Xbar.property U).obj F
  let : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
  let : IsIso (compactificationFShriekMap B fbar U F).val :=
    compactificationFShriekMap_isIso B fbar U F
  let : IsIso (fShriekSubsheaf B fbar Fbar).val.arrow :=
    fShriekSubsheaf_arrow_isIso B fbar Fbar
  infer_instance

/-- **Stacks 0F52.** The compactification comparison commutes with morphisms of abelian étale
sheaves, hence identifies the two direct-image functors naturally. -/
@[stacks 0F52 "naturality and functor comparison"]
public theorem compactificationFShriekMap_naturality
    (H : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) AddCommGrpCat.{u + 1})
    (phi : F ⟶ H) :
    letI : IsSeparated (B.inclusion.map fbar) := inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar)) := by
      change LocallyOfFiniteType (B.inclusion.map U.obj.hom ≫ B.inclusion.map fbar)
      infer_instance
    let ext := abelianExtensionByZero B Xbar.obj Xbar.property U
    let push := (smallEtaleBaseChange B (U.obj.hom ≫ fbar)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    let pushbar := (smallEtaleBaseChange B fbar).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Xbar.obj Xbar.property)
    let GF := (fShriekSubsheaf B (U.obj.hom ≫ fbar) F).val
    let GH := (fShriekSubsheaf B (U.obj.hom ≫ fbar) H).val
    let GbarF := (fShriekSubsheaf B fbar (ext.obj F)).val
    let GbarH := (fShriekSubsheaf B fbar (ext.obj H)).val
    ∀ (a : GF.obj.left ⟶ GH.obj.left) (b : GbarF.obj.left ⟶ GbarH.obj.left),
      (a ≫ GH.arrow = GF.arrow ≫ push.map phi) →
      (b ≫ GbarH.arrow = GbarF.arrow ≫ pushbar.map (ext.map phi)) →
      (a ≫ (compactificationFShriekMap B fbar U H).val =
        (compactificationFShriekMap B fbar U F).val ≫ b) := by
  intro ext push pushbar GF GH GbarF GbarH a b ha hb
  let : IsSeparated (B.inclusion.map fbar) := inferInstance
  let : LocallyOfFiniteType (B.inclusion.map fbar) := inferInstance
  let : LocallyOfFiniteType (B.inclusion.map (U.obj.hom ≫ fbar)) := by
    show LocallyOfFiniteType (B.inclusion.map U.obj.hom ≫ B.inclusion.map fbar)
    infer_instance
  let Fbar := ext.obj F
  let Hbar := ext.obj H
  let pull := (smallEtaleBaseChange B U.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Xbar.obj Xbar.property)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
  let GpullF := (fShriekSubsheaf B (U.obj.hom ≫ fbar) (pull.obj Fbar)).val
  let GpullH := (fShriekSubsheaf B (U.obj.hom ≫ fbar) (pull.obj Hbar)).val
  let unitF := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app F
  let unitH := (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.app H
  let isoF := (openRestrictionIso.{u, u} B U.obj.hom).hom.app Fbar
  let isoH := (openRestrictionIso.{u, u} B U.obj.hom).hom.app Hbar
  let eF := unitF ≫ isoF
  let eH := unitH ≫ isoH
  let extMap := ext.map phi
  let n := (fShriekMap B (U.obj.hom ≫ fbar) (pull.obj Fbar) (pull.obj Hbar)
    (pull.map extMap)).val
  let iF := (fShriekMap B (U.obj.hom ≫ fbar) F (pull.obj Fbar) eF).val
  let iH := (fShriekMap B (U.obj.hom ≫ fbar) H (pull.obj Hbar) eH).val
  have hmapF : iF ≫ GpullF.arrow = GF.arrow ≫ push.map eF :=
    (fShriekMap B (U.obj.hom ≫ fbar) F (pull.obj Fbar) eF).property
  have hmapH : iH ≫ GpullH.arrow = GH.arrow ≫ push.map eH :=
    (fShriekMap B (U.obj.hom ≫ fbar) H (pull.obj Hbar) eH).property
  have hn : n ≫ GpullH.arrow = GpullF.arrow ≫ push.map (pull.map extMap) :=
    (fShriekMap B (U.obj.hom ≫ fbar) (pull.obj Fbar) (pull.obj Hbar) (pull.map extMap)).property
  have heta : phi ≫ eH = eF ≫ pull.map extMap := by
    show phi ≫ unitH ≫ isoH = unitF ≫ isoF ≫ pull.map extMap
    have hunit : phi ≫ unitH =
        unitF ≫ (abelianRestriction B Xbar.obj Xbar.property U).map (ext.map phi) :=
      (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U).unit.naturality phi
    exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ isoH) hunit).trans <|
      (Category.assoc _ _ _).trans <| congrArg (unitF ≫ ·)
        ((openRestrictionIso.{u, u} B U.obj.hom).hom.naturality (ext.map phi))
  have hi : a ≫ iH = iF ≫ n := by
    apply (cancel_mono GpullH.arrow).1
    simp only [Category.assoc, hmapH, hn]
    rw [reassoc_of% ha, ← push.map_comp, heta, push.map_comp, reassoc_of% hmapF]
  have hb' : b = (fShriekMap B fbar Fbar Hbar extMap).val :=
    (cancel_mono GbarH.arrow).1 (hb.trans (fShriekMap B fbar Fbar Hbar extMap).property.symm)
  dsimp [compactificationFShriekMap]
  let openF := (openInclusionShriekMap B U.obj.hom fbar Fbar).val
  let openH := (openInclusionShriekMap B U.obj.hom fbar Hbar).val
  show a ≫ (iH ≫ openH) = (iF ≫ openF) ≫ b
  rw [← Category.assoc, hi, Category.assoc, Category.assoc, hb']
  exact congrArg (iF ≫ ·) (openInclusionShriekMap_naturality B U.obj.hom fbar Fbar Hbar extMap)

end Compactification

end AlgebraicGeometry.SmallEtale

end
