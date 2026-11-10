module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.PointFixingAut
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Automorphisms.PointwiseTrivial

/-!
# An automorphism of a curve over a finite field fixing every point has finite order

Let `k` be a finite field and let `X` be a curve over `k`. An automorphism of `X` over `k` which
fixes every point of the underlying topological space has finite order.

This is the second half of the input that the finite-field case of [Stacks, Tag 0G05] needs. The
first half is `AlgebraicGeometry.finite_pointFixingAutSubgroup_of_normal_curve`, the finiteness of
the point-fixing automorphism group of a *normal projective* curve. The passage from there to an
arbitrary curve is the equivalence of categories (2) and (3) of [Stacks, Tag 0BY1],
`AlgebraicGeometry.normalProjectiveCurveEquivalenceCurve`: the automorphism is transported to the
normal projective model, where it need no longer fix every point, but where it can move only
finitely many of them, because it agrees with the given automorphism on a dense open subscheme
and the complement of the image of a dominant morphism of curves is finite. A permutation with
finite support has finite order, so some power of the transported automorphism does fix every
point, and that power lies in a finite group.

## Main results

* `AlgebraicGeometry.finite_moved_points_of_rational_intertwining`: an automorphism intertwined,
  through a dominant rational map of curves, with one which fixes every point moves only finitely
  many points.
* `AlgebraicGeometry.isOfFinOrder_of_finite_pointFixingAutSubgroup`: an automorphism moving only
  finitely many points has finite order as soon as the point-fixing automorphisms form a finite
  group.
* `AlgebraicGeometry.isOfFinOrder_curveAut_of_fixes_points`: **the finite order**, for a curve
  over a finite field.
* `AlgebraicGeometry.exists_iterate_comp_eq_id_of_fixes_points`: the same statement in the shape
  the disjunctive hypothesis of `AlgebraicGeometry.eq_id_of_eq_on_points` asks for.
* `AlgebraicGeometry.eq_id_of_eq_on_points_of_isCurve`: clause (2) of [Stacks, Tag 0G05] for a
  curve, over an arbitrary field and with nothing carried.

## Implementation notes

An automorphism of the scheme over `k` is an element of `Aut (Over.mk p)`; the corresponding
automorphism in category (2) of Tag 0BY1 — a curve and its dominant rational maps — is
`AlgebraicGeometry.curveAutOfOverAut`, and it determines the original one because a morphism of
integral schemes into a separated one is determined by its rational map.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ### Automorphisms of a curve and of its underlying scheme -/

/-- Composition of the rational maps of two morphisms, the first dominant, is the rational map of
the composition. -/
lemma toRationalMap_comp' {X Y Z : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⟶ Y) [IsDominant f] (g : Y ⟶ Z) :
    f.toRationalMap.comp g.toRationalMap = (f ≫ g).toRationalMap := by
  rw [Scheme.RationalMap.comp_toRationalMap]
  rfl

/-- A morphism over `S` out of an integral scheme into a scheme separated over `S` is determined
by its rational map. -/
@[ega "II 7.3.3" "partial"]
private lemma overHom_eq_of_toRationalMap_eq {S : Scheme.{u}} {X Y : Over S} [IsIntegral X.left]
    [IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : f.left.toRationalMap = g.left.toRationalMap) : f = g := by
  obtain ⟨U, hU, hUl, hUr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h
  change X.left.homOfLE hUl ≫ f.left.toPartialMap.hom =
    X.left.homOfLE hUr ≫ g.left.toPartialMap.hom at hEq
  have hfgU : U.ι ≫ f.left = U.ι ≫ g.left := by
    calc
      U.ι ≫ f.left = X.left.homOfLE hUl ≫ f.left.toPartialMap.hom := by
        simp [Scheme.Hom.toPartialMap, Scheme.topIso_hom, ← Scheme.homOfLE_ι X.left hUl]
      _ = X.left.homOfLE hUr ≫ g.left.toPartialMap.hom := hEq
      _ = U.ι ≫ g.left := by
        simp [Scheme.Hom.toPartialMap, Scheme.topIso_hom, ← Scheme.homOfLE_ι X.left hUr]
  exact eq_of_isSchemeTheoreticallyDense f g U (((dense_open_tfae U).out 1 3).mp hU) hfgU

/-- The automorphism of a curve, as an object of category (2) of Tag 0BY1, attached to an
automorphism of the underlying scheme over the base field. -/
noncomputable def curveAutOfOverAut (C : Curve k) (a : Aut (Over.mk C.obj.structureMap)) :
    Aut C := by
  letI : IsIso a.asIso.hom := ⟨a.asIso.inv, a.asIso.hom_inv_id, a.asIso.inv_hom_id⟩
  letI : IsIso a.asIso.inv := ⟨a.asIso.hom, a.asIso.inv_hom_id, a.asIso.hom_inv_id⟩
  letI : IsIso a.asIso.hom.left := (Over.forget _).map_isIso a.asIso.hom
  letI : IsIso a.asIso.inv.left := (Over.forget _).map_isIso a.asIso.inv
  letI : a.asIso.hom.left.IsOver (Spec (.of k)) := ⟨Over.w a.asIso.hom⟩
  letI : a.asIso.inv.left.IsOver (Spec (.of k)) := ⟨Over.w a.asIso.inv⟩
  refine Aut.of
    { hom := ObjectProperty.homMk ⟨a.asIso.hom.left.toRationalMap⟩
      inv := ObjectProperty.homMk ⟨a.asIso.inv.left.toRationalMap⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    change a.asIso.hom.left.toRationalMap.comp a.asIso.inv.left.toRationalMap = _
    rw [toRationalMap_comp', ← Over.comp_left, a.asIso.hom_inv_id]
    rfl
  · apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    change a.asIso.inv.left.toRationalMap.comp a.asIso.hom.left.toRationalMap = _
    rw [toRationalMap_comp', ← Over.comp_left, a.asIso.inv_hom_id]
    rfl

/-- An automorphism of the scheme underlying a curve is determined by the automorphism it induces
in category (2) of Tag 0BY1. -/
theorem curveAutOfOverAut_injective (C : Curve k) : Function.Injective (curveAutOfOverAut C) := by
  intro a b hab
  apply Aut.ext
  apply Iso.ext
  have : IsIntegral (Over.mk C.obj.structureMap).left := C.obj.isVariety.toIsIntegral
  have : IsSeparated (Over.mk C.obj.structureMap).hom := C.obj.isVariety.toIsSeparated
  exact overHom_eq_of_toRationalMap_eq a.asIso.hom b.asIso.hom
    (congrArg (fun e : Aut C ↦ e.asIso.hom.hom.toRationalMap) hab)

/-- `AlgebraicGeometry.curveAutOfOverAut` as a homomorphism of groups. -/
noncomputable def curveAutMonoidHom (C : Curve k) :
    Aut (Over.mk C.obj.structureMap) →* Aut C where
  toFun := curveAutOfOverAut C
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    rfl
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Variety.Hom.ext
    have : IsIso b.asIso.hom := ⟨b.asIso.inv, b.asIso.hom_inv_id, b.asIso.inv_hom_id⟩
    have : IsIso b.asIso.hom.left := (Over.forget _).map_isIso b.asIso.hom
    change (b.asIso.hom.left ≫ a.asIso.hom.left).toRationalMap =
      b.asIso.hom.left.toRationalMap.comp a.asIso.hom.left.toRationalMap
    exact (toRationalMap_comp' _ _).symm

/-- A faithful functor is injective on automorphism groups. -/
private lemma mapAut_injective {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Faithful]
    (X : C) : Function.Injective (F.mapAut X) :=
  fun _ _ h ↦ Aut.ext (Iso.ext (F.map_injective (congrArg (fun e ↦ e.asIso.hom) h)))

/-! ### Automorphisms moving finitely many points -/

/-- A permutation with finite support has finite order. -/
private lemma isOfFinOrder_perm_of_finite_support {α : Type*} (e : Equiv.Perm α)
    (he : {x | e x ≠ x}.Finite) : IsOfFinOrder e := by
  classical
  have : Finite {x // e x ≠ x} := he.to_subtype
  have hinv (x : α) : e (e x) ≠ e x ↔ e x ≠ x := e.injective.ne_iff
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (e.subtypePerm (p := fun x ↦ e x ≠ x) hinv)).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  ext x
  by_cases hx : e x = x
  · exact (show Function.IsFixedPt e x from hx).iterate n
  · have hh := congrArg (fun f : Equiv.Perm {x // e x ≠ x} ↦ (f ⟨x, hx⟩).val) hpow
    rwa [Equiv.Perm.subtypePerm_pow] at hh

/-- The permutation of the underlying space induced by an automorphism over the base. -/
noncomputable def pointPermutation {X S : Scheme.{u}} (p : X ⟶ S) :
    Aut (Over.mk p) →* Equiv.Perm X where
  toFun a := (Scheme.homeoOfIso ((Over.forget S).mapIso a.asIso)).toEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- An automorphism moving only finitely many points has finite order, as soon as the
automorphisms fixing every point form a finite group: a power of it fixes every point. -/
theorem isOfFinOrder_of_finite_pointFixingAutSubgroup {X S : Scheme.{u}} (p : X ⟶ S)
    [Finite (pointFixingAutSubgroup p)] (a : Aut (Over.mk p))
    (ha : {x | a.asIso.hom.left x ≠ x}.Finite) : IsOfFinOrder a := by
  obtain ⟨n, hn, hp⟩ :=
    (isOfFinOrder_perm_of_finite_support (pointPermutation p a) ha).exists_pow_eq_one
  have hmem : a ^ n ∈ pointFixingAutSubgroup p := by
    intro x
    have hh := congrArg (fun e : Equiv.Perm X ↦ e x) hp
    rwa [← map_pow] at hh
  exact ((pointFixingAutSubgroup p).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨a ^ n, hmem⟩ : pointFixingAutSubgroup p))).of_pow hn.ne'

/-- A closed subset of a Noetherian integral scheme of dimension at most one which misses the
generic point is finite. -/
private lemma finite_closed_of_genericPoint_not_mem (X : Scheme.{u}) [IsIntegral X]
    [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1) {s : Set X} (hs : IsClosed s)
    (hη : genericPoint X ∉ s) : s.Finite := by
  classical
  have hdim : Order.krullDim X ≤ 1 := by
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  obtain ⟨S, hS, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine hS.sUnion fun t ht ↦ ?_
  have htg := (hSi t ht).isGenericPoint_genericPoint (hSc t ht)
  let z := (hSi t ht).genericPoint
  have hz : z ≠ genericPoint X := fun he ↦ hη (Set.mem_sUnion.mpr ⟨t, ht, he ▸ htg.mem⟩)
  have hm : IsMin z := by
    rcases Order.krullDim_le_one_iff.mp hdim z with hm | hm
    · exact hm
    · exact (hz ((Specializes.antisymm (hm (show z ≤ (genericPoint X) from le_top))
        (genericPoint_specializes z)).eq)).elim
  exact (Set.finite_singleton z).subset fun x hx ↦ Set.mem_singleton_iff.mpr
    (Specializes.antisymm (hm (htg.specializes hx)) (htg.specializes hx)).eq

/-- A constructible subset of a Noetherian integral scheme of dimension at most one which
contains the generic point has finite complement. -/
private lemma finite_compl_of_isConstructible_of_genericPoint_mem (X : Scheme.{u}) [IsIntegral X]
    [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1) {s : Set X}
    (hs : Topology.IsConstructible s) (hη : genericPoint X ∈ s) : sᶜ.Finite := by
  have hall : (genericPoint X ∈ s → sᶜ.Finite) ∧ (genericPoint X ∉ s → s.Finite) := by
    clear hη
    induction hs using Topology.IsConstructible.empty_union_induction with
    | open_retrocompact U hU hc =>
      refine ⟨fun hη ↦ ?_, fun hη ↦ ?_⟩
      · exact finite_closed_of_genericPoint_not_mem X hX hU.isClosed_compl (by simpa)
      · have hu : U = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
          hη (((genericPoint_spec X).mem_open_set_iff hU).mpr ⟨x, trivial, hx⟩)
        simp [hu]
    | union s hs t ht ihs iht =>
      refine ⟨fun hη ↦ ?_, fun hη ↦ (ihs.2 (hη ∘ Or.inl)).union (iht.2 (hη ∘ Or.inr))⟩
      rcases hη with hη | hη
      · exact (ihs.1 hη).subset (Set.compl_subset_compl.mpr Set.subset_union_left)
      · exact (iht.1 hη).subset (Set.compl_subset_compl.mpr Set.subset_union_right)
    | compl s hs ih => simpa only [compl_compl, Set.mem_compl_iff, not_not] using ih.symm
  exact hall.1 hη

/-- The complement of the image of a dominant morphism of finite presentation into a Noetherian
integral scheme of dimension at most one is finite: the image is constructible and contains the
generic point. -/
private lemma finite_compl_range_of_dominant_curve {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace Y] (hY : topologicalKrullDim Y ≤ 1) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [IsDominant f] :
    (Set.range f)ᶜ.Finite :=
  finite_compl_of_isConstructible_of_genericPoint_mem Y hY
    (by simpa using f.isConstructible_image Topology.IsConstructible.univ)
    ⟨genericPoint X, genericPoint_eq_of_isDominant f⟩

/-- An automorphism fixing every point, intertwined with another one through a dominant partial
map, fixes the image of that partial map over a dense open subscheme. -/
private lemma exists_dense_partialMap_fixed_image {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) [IsIso f] (g : Y ⟶ Y) (hpoints : ∀ x, f x = x) (r : X.PartialMap Y)
    [IsDominant r.hom]
    (hr : f.toRationalMap.comp r.toRationalMap = r.toRationalMap.comp g.toRationalMap) :
    ∃ (U : X.Opens) (_hU : Dense (U : Set X)) (hle : U ≤ r.domain),
      ∀ x : U, g ((X.homOfLE hle ≫ r.hom) x) = (X.homOfLE hle ≫ r.hom) x := by
  have he : (f.toPartialMap.comp r).equiv (r.compHom g) := by
    apply Scheme.PartialMap.toRationalMap_eq_iff.mp
    rw [← Scheme.RationalMap.toRationalMap_comp, Scheme.RationalMap.compHom_toRationalMap]
    simpa only [Scheme.RationalMap.comp_toRationalMap] using hr
  obtain ⟨U, hU, h₁, h₂, hh⟩ := he
  refine ⟨U, hU, h₂, fun x ↦ ?_⟩
  have hx := congrArg (fun a : U.toScheme ⟶ Y ↦ a x) hh
  change (X.homOfLE h₁ ≫ (f.toPartialMap.comp r).hom) x = (X.homOfLE h₂ ≫ r.hom ≫ g) x at hx
  change (X.homOfLE h₂ ≫ r.hom ≫ g) x = _
  rw [← hx]
  have hmor : (f.toPartialMap.domain.ι.isoImage (f.toPartialMap.hom ⁻¹ᵁ r.domain)).inv ≫
      (f.toPartialMap.hom ∣_ r.domain) ≫ r.domain.ι =
      (f.toPartialMap.domain.ι ''ᵁ (f.toPartialMap.hom ⁻¹ᵁ r.domain)).ι ≫ f := by
    rw [morphismRestrict_ι]
    exact Scheme.Hom.isoImage_inv_ι_assoc _ _ f
  have hpt : ((f.toPartialMap.domain.ι.isoImage (f.toPartialMap.hom ⁻¹ᵁ r.domain)).inv ≫
      f.toPartialMap.hom ∣_ r.domain) ((X.homOfLE h₁) x) = (X.homOfLE h₂) x := by
    apply Subtype.ext
    refine (congrArg (fun m ↦ m ((X.homOfLE h₁) x)) hmor).trans ?_
    change f (((X.homOfLE h₁) x).1) = ((X.homOfLE h₂) x).1
    rw [Scheme.homOfLE_apply, Scheme.homOfLE_apply]
    exact hpoints _
  rw [Scheme.PartialMap.comp_hom]
  exact congrArg r.hom hpt

/-- A scheme of finite type over a field is Noetherian. -/
private lemma isNoetherian_of_finiteType_over (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  ⟨⟩

/-- **An automorphism of a curve intertwined, through a dominant rational map, with an
automorphism fixing every point moves only finitely many points.** The two agree on a dense open
subscheme of the source, whose image misses only finitely many points of the target. -/
theorem finite_moved_points_of_rational_intertwining (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hY : topologicalKrullDim Y ≤ 1) (f : X ⟶ X) [IsIso f] (g : Y ⟶ Y) (hpoints : ∀ x, f x = x)
    (r : X ⤏ Y) [r.IsDominant] [r.IsOver (Spec (.of k))]
    (hr : f.toRationalMap.comp r = r.comp g.toRationalMap) : {y | g y ≠ y}.Finite := by
  have := isNoetherian_of_finiteType_over k X
  have := isNoetherian_of_finiteType_over k Y
  obtain ⟨r, hrOver, rfl⟩ := r.exists_partialMap_over (Spec (.of k))
  have : r.IsOver (Spec (.of k)) := hrOver
  have : IsDominant r.hom := r.isDominant_toRationalMap_iff.mp inferInstance
  obtain ⟨U, hU, hle, hfix⟩ := exists_dense_partialMap_fixed_image f g hpoints r hr
  have : Nonempty U := hU.nonempty.to_subtype
  have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace ↥(U : Set X))
  let l : U.toScheme ⟶ Y := (r.restrict U hU hle).hom
  have : l.IsOver (Spec (.of k)) := inferInstanceAs ((r.restrict U hU hle).IsOver _)
  have : IsDominant l := inferInstanceAs (IsDominant (r.restrict U hU hle).hom)
  have : LocallyOfFiniteType (l ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    change LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of k))
    infer_instance
  have : LocallyOfFiniteType l := locallyOfFiniteType_of_comp l (Y ↘ Spec (.of k))
  apply (finite_compl_range_of_dominant_curve hY l).subset
  rintro y hy ⟨x, rfl⟩
  exact hy (hfix x)

/-! ### Finite order -/

/-- **An automorphism of a curve over a finite field which fixes every point of the underlying
topological space has finite order.**

This is the input the finite-field case of [Stacks, Tag 0G05] needs, in the form the source gives
it: "a curve over a finite field has a finite automorphism group". The automorphism is carried by
the equivalence of categories (2) and (3) of [Stacks, Tag 0BY1] to the normal projective model,
where it moves only finitely many points, so a power of it fixes every point; the point-fixing
automorphisms of a normal projective curve over a finite field form a finite group. -/
theorem isOfFinOrder_curveAut_of_fixes_points [Finite k] (C : Curve k)
    (a : Aut (Over.mk C.obj.structureMap)) (ha : ∀ x, a.asIso.hom.left x = x) : IsOfFinOrder a := by
  let E := normalProjectiveCurveEquivalenceCurve k
  let P : NormalProjectiveCurve k := E.inverse.obj C
  let b : Aut P := E.inverse.mapAut C (curveAutOfOverAut C a)
  let F : NormalProjectiveCurve k ⥤ Over (Spec (.of k)) :=
    ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _
  let d : Aut (F.obj P) := F.mapAut P b
  let D : Curve k := (normalProjectiveCurveToCurve k).obj P
  obtain ⟨hPcurve, hPproj, hPnormal⟩ := P.property
  have : IsCurve k D.obj.structureMap := hPcurve
  have : IsNormal D.obj.toScheme := hPnormal
  have : IsProper D.obj.structureMap := isProper_of_isProjectiveMorphism _ hPproj
  have : IsCurve k C.obj.structureMap := C.property
  have : IsIso a.asIso.hom := ⟨a.asIso.inv, a.asIso.hom_inv_id, a.asIso.inv_hom_id⟩
  have : IsIso a.asIso.hom.left := (Over.forget _).map_isIso a.asIso.hom
  have hdimD : topologicalKrullDim D.obj.toScheme ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := D.obj.structureMap)).le
  -- the intertwining rational map: the counit of the equivalence
  let i : D ≅ C := E.counitIso.app C
  have hnat := E.counitIso.inv.naturality (curveAutOfOverAut C a).asIso.hom
  have hmoved : {y | d.asIso.hom.left y ≠ y}.Finite := by
    have (E : Curve k) : LocallyOfFiniteType (E.obj.toScheme ↘ Spec (.of k)) ∧
        QuasiCompact (E.obj.toScheme ↘ Spec (.of k)) :=
      ⟨inferInstanceAs (LocallyOfFiniteType E.obj.structureMap),
        inferInstanceAs (QuasiCompact E.obj.structureMap)⟩
    obtain ⟨_, _⟩ := this C
    obtain ⟨_, _⟩ := this D
    exact finite_moved_points_of_rational_intertwining k
      (X := C.obj.toScheme) (Y := D.obj.toScheme) hdimD
      a.asIso.hom.left d.asIso.hom.left ha i.inv.hom.toRationalMap
      (congrArg (fun q : C ⟶ D ↦ q.hom.toRationalMap) hnat)
  have : Finite (pointFixingAutSubgroup (F.obj P).hom) :=
    finite_pointFixingAutSubgroup_of_normal_curve k D.obj.toScheme D.obj.structureMap hdimD
  have hd : IsOfFinOrder d := isOfFinOrder_of_finite_pointFixingAutSubgroup (F.obj P).hom d hmoved
  have hb : IsOfFinOrder b := (mapAut_injective F P).isOfFinOrder_iff.mp hd
  have hC : IsOfFinOrder (curveAutOfOverAut C a) :=
    (mapAut_injective E.inverse C).isOfFinOrder_iff.mp hb
  exact (curveAutOfOverAut_injective C).isOfFinOrder_iff (f := curveAutMonoidHom C) |>.mp hC

/-- **An automorphism of a curve over a finite field fixing every point has an iterate equal to
the identity**, in the shape the disjunctive hypothesis of
`AlgebraicGeometry.eq_id_of_eq_on_points` asks for. -/
theorem exists_iterate_comp_eq_id_of_fixes_points [Finite k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsCurve k p] (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p)
    (hpoints : ∀ x, f x = x) :
    ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X := by
  let C : Curve k := ⟨{ toScheme := X, structureMap := p }, ‹IsCurve k p›⟩
  let g : Over.mk p ⟶ Over.mk p := Over.homMk f hf
  have : IsIso g := by
    have : IsIso ((Over.forget _).map g) := inferInstanceAs (IsIso f)
    exact isIso_of_reflects_iso g (Over.forget _)
  let a : Aut (Over.mk C.obj.structureMap) := .of (asIso g)
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_curveAut_of_fixes_points C a hpoints).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have hiter (m : ℕ) : (fun h : X ⟶ X ↦ h ≫ f)^[m] (𝟙 X) = ((a ^ m).asIso.hom.left : X ⟶ X) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  rw [hiter n, hpow]
  rfl

/-- **Clause (2) of [Stacks, Tag 0G05] for a curve**, over an arbitrary field and with nothing
carried: an automorphism over `k` of a curve over `k` which fixes every point of the underlying
topological space is the identity.

Over an infinite field this is `AlgebraicGeometry.eq_id_of_isIntegral_of_eq_on_points`, which
needs no hypothesis on the automorphism. Over a finite field that statement is false for an
endomorphism — the `p`-power Frobenius of the affine line fixes every point, which is
`AlgHom.exists_comap_eq_ne_id_of_finite_field` — and it is the finite order of an *automorphism*,
`AlgebraicGeometry.isOfFinOrder_curveAut_of_fixes_points`, that discharges the disjunctive
hypothesis there.

This is not the whole of clause (2), which is about a reduced scheme of finite type all of whose
irreducible components have positive dimension; the reduction of that statement to curves is not
proved here. -/
theorem eq_id_of_eq_on_points_of_isCurve {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsCurve k p]
    (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p) (hpoints : ∀ x, f x = x) : f = 𝟙 X := by
  have hdim : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  have hk : Infinite k ∨ ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X := by
    rcases finite_or_infinite k with hfin | hinf
    · exact Or.inr (exists_iterate_comp_eq_id_of_fixes_points p f hf hpoints)
    · exact Or.inl hinf
  exact eq_id_of_isIntegral_of_eq_on_points p f hf hpoints (hdim ▸ zero_lt_one) hk

end AlgebraicGeometry

end
