module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.UnitSeries
public import StacksFrontier.CategoryTheory.Preadditive.AdditiveFunctorBiprod
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The comparison map of the family of irreducible components, on a stalk

Let `X` be a Noetherian scheme and let `Zⱼ ⟶ X` be its irreducible components, each with the
subscheme structure of `AlgebraicGeometry.Scheme.irreducibleComponent` — the closed subscheme
cut out by the kernel of the restriction to the complement of the other components. Paragraph 1
of [Stacks, Tag 0AYW] needs the comparison map

`𝒪_X ⟶ ⊕_{j<N} (iⱼ)_*𝒪_{Zⱼ}`

to be bijective on the stalk at every point outside a finite set of closed points. This file
proves that, and the exceptional set is the locus where two components meet.

The local computation is the whole content. At a point `x` lying on only one component `Zⱼ₀`:

* every other summand has vanishing stalk at `x`, because `x` is off the image of a closed
  immersion ([Stacks, Tag 00AE]);
* the surviving summand's component of the comparison map is the adjunction unit
  `𝒪_X ⟶ (i_{j₀})_*𝒪_{Z_{j₀}}`, whose stalk, read through the two canonical identifications, is
  the stalk map of `i_{j₀}`; and that stalk map is bijective, because `x` lies in the open set
  `AlgebraicGeometry.Scheme.irreducibleComponentOpen` on which the component's ideal sheaf is
  the kernel of the *open* immersion of that open set, through which the component's inclusion
  therefore factors;
* so the map into the biproduct is inverted by the stalk functor, which is additive.

## Main results

* `AlgebraicGeometry.exists_bijective_stalkMap_irreducibleComponentι`: the local ring of `X` at
  a point of only one component is the local ring of that component.
* `AlgebraicGeometry.bijective_stalk_unitToPushforwardObjUnit`: the stalk of the adjunction unit
  of a closed immersion is bijective where the stalk map is.
* `AlgebraicGeometry.isIso_map_biprodSeriesLift`: an additive functor inverts the universal map
  into a series of biproducts as soon as exactly one summand survives.
* `AlgebraicGeometry.bijective_stalk_pushforwardUnitSeriesMap_of_forall_notMemRange`: the three
  previous items combined, for an arbitrary finite family of closed subschemes.
* `AlgebraicGeometry.exists_finite_bijective_stalk_pushforwardUnitSeriesMap_irreducibleComponent`:
  the conclusion at the family of irreducible components, with the exceptional set exhibited as
  finite and consisting of closed points.

## Implementation notes

**The stalk functor is used at two spellings of its source.**
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x` is typed on
`SheafOfModules X.ringCatSheaf`, and at that spelling instance search finds neither
`HasZeroMorphisms` nor the binary biproducts — `AlgebraicGeometry.Scheme.Modules` is a
definition, and the instances are declared at it: `HasBinaryBiproduct A B` for
`A B : X.Modules` is found and the same goal for `A B : SheafOfModules X.ringCatSheaf` is not.
So `isZero_map_biprodSeries` and `isIso_map_biprodSeriesLift` are stated for an arbitrary
additive functor out of `X.Modules`, and `additive_stalkAddCommGroupFunctor_modules` transports
the additivity to that spelling; the functor itself is unchanged.

**The finiteness of the exceptional set is purely topological** and is taken from
`StacksFrontier/Topology/Dimension/DimensionLEOne.lean`: the locus where two components meet is a
closed set containing no irreducible component — each component has its generic point off it,
by `Stacks.Topology.Irreducible.genericPoint_mem_disjointLocus` — and in a Noetherian sober
`T0` space of Krull dimension at most one such a set is finite and consists of closed points.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0BA8](https://stacks.math.columbia.edu/tag/0BA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed immersion that a morphism injective on stalks factors through is bijective on
stalks at the image point.** -/
theorem bijective_stalkMap_of_injective_stalkMap_comp {W X Y : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (g : Y ⟶ W) (y : Y)
    (h : Function.Injective ((g ≫ i).stalkMap y)) :
    Function.Bijective (i.stalkMap (g.base y)) := by
  refine ⟨fun a b hab => ?_, Scheme.Hom.stalkMap_surjective i _⟩
  have h2 : Function.Injective (i.stalkMap (g.base y) ≫ g.stalkMap y) := by
    rwa [← Scheme.Hom.stalkMap_comp]
  exact h2 (by rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hab])

/-- The image of the inclusion of an irreducible component is that component. -/
theorem range_irreducibleComponentι (X : Scheme.{u}) [IsNoetherian X] (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) :
    Set.range (X.irreducibleComponentι Z hZ).base = Z :=
  (X.irreducibleComponentIdeal Z hZ).range_subschemeι

/-- **The local ring of `X` at a point lying on only one irreducible component is the local ring
of that component.** -/
theorem exists_bijective_stalkMap_irreducibleComponentι (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) (x : X)
    (hx : x ∈ X.irreducibleComponentOpen Z) :
    ∃ z : X.irreducibleComponent Z hZ, X.irreducibleComponentι Z hZ z = x ∧
      Function.Bijective ((X.irreducibleComponentι Z hZ).stalkMap z) := by
  have hle : X.irreducibleComponentIdeal Z hZ ≤ (X.irreducibleComponentOpen Z).ι.ker :=
    (X.irreducibleComponentIdeal_def Z hZ).le
  let g : (X.irreducibleComponentOpen Z).toScheme ⟶ X.irreducibleComponent Z hZ :=
    (X.irreducibleComponentOpen Z).ι.toImage ≫ Scheme.IdealSheafData.inclusion hle
  have hg : g ≫ X.irreducibleComponentι Z hZ = (X.irreducibleComponentOpen Z).ι := by
    change ((X.irreducibleComponentOpen Z).ι.toImage ≫ Scheme.IdealSheafData.inclusion hle) ≫
      (X.irreducibleComponentIdeal Z hZ).subschemeι = _
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact Scheme.Hom.toImage_imageι _
  let y : (X.irreducibleComponentOpen Z).toScheme := ⟨x, hx⟩
  refine ⟨g.base y, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hg]
    rfl
  · refine bijective_stalkMap_of_injective_stalkMap_comp _ g y ?_
    rw [hg]
    exact (ConcreteCategory.bijective_of_isIso _).1

/-! ### The stalk of the adjunction unit at a point of the image -/

/-- **The stalk of `𝒪_X ⟶ i_*𝒪_Z` is the stalk map of `i`**, read through the two
identifications: `Stacks.Chow.stalkPushforwardComparison` for the direct image and
`Stacks.Ample.unitStalkFun` for the structure sheaf as a module over itself. Both sides are
checked on the germ of a section, where both are the comorphism `i^♯` of `i`. -/
theorem unitStalkFun_stalkPushforwardComparison_stalk_unitToPushforwardObjUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z)
    (s : (Stacks.Ample.unitModule X).presheaf.stalk (i z)) :
    Stacks.Ample.unitStalkFun Z z (Stacks.Chow.stalkPushforwardComparison i
        (Stacks.Ample.unitModule Z) z (ConcreteCategory.hom
          ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf (i z)).map
            (_root_.SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) s)) =
      i.stalkMap z (Stacks.Ample.unitStalkFun X (i z) s) := by
  obtain ⟨V, hV, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (Stacks.Ample.unitModule X).presheaf s
  have h1 : ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf (i z)).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))
      (((Stacks.Ample.unitModule X).presheaf.germ V (i z) hV) a) =
      (((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).presheaf.germ V (i z) hV)
        (show Γ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z), V) from
          i.app V (show Γ(X, V) from a)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V (i z) hV _ a
  rw [h1, Stacks.Chow.stalkPushforwardComparison_germ i (Stacks.Ample.unitModule Z) z V hV _,
    Stacks.Ample.unitStalkFun_germ X (i z) V hV a,
    i.germ_stalkMap_apply V z hV (show Γ(X, V) from a)]
  exact Stacks.Ample.unitStalkFun_germ Z z (i ⁻¹ᵁ V) hV _

/-- **At a point of the image where `i` is bijective on local rings the unit `𝒪_X ⟶ i_*𝒪_Z` is
bijective on stalks.** -/
theorem bijective_stalk_unitToPushforwardObjUnit {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base))
    (hb : Function.Bijective (i.stalkMap z)) :
    Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf (i z)).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))) := by
  have key := unitStalkFun_stalkPushforwardComparison_stalk_unitToPushforwardObjUnit i z
  refine ⟨fun p q hpq => ?_, fun c => ?_⟩
  · refine (Stacks.Chow.bijective_unitStalkFun X (i z)).1 (hb.1 ?_)
    rw [← key p, ← key q, hpq]
  · obtain ⟨r, hr⟩ := hb.2 (Stacks.Ample.unitStalkFun Z z
      (Stacks.Chow.stalkPushforwardComparison i (Stacks.Ample.unitModule Z) z c))
    obtain ⟨p, hp⟩ := (Stacks.Chow.bijective_unitStalkFun X (i z)).2 r
    refine ⟨p, (Stacks.Chow.bijective_stalkPushforwardComparison i _ z hi).1
      ((Stacks.Chow.bijective_unitStalkFun Z z).1 ?_)⟩
    rw [key p, hp, hr]

/-! ### The stalk of the universal map into a series of biproducts -/

section Series

/-- **The stalk functor to abelian groups is additive.** It is the composite of three additive
functors, which instance search does not see because
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor` is a plain definition. -/
theorem additive_stalkAddCommGroupFunctor {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (t : T) :
    (SheafOfModules.stalkAddCommGroupFunctor O t).Additive := by
  refine ⟨fun {M N} f g => ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} t).map
      ((PresheafOfModules.toPresheaf O.obj).map
        ((_root_.SheafOfModules.forget O).map (f + g))) =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} t).map
        ((PresheafOfModules.toPresheaf O.obj).map
          ((_root_.SheafOfModules.forget O).map f)) +
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} t).map
        ((PresheafOfModules.toPresheaf O.obj).map
          ((_root_.SheafOfModules.forget O).map g))
  rw [Functor.map_add (F := _root_.SheafOfModules.forget O),
    Functor.map_add (F := PresheafOfModules.toPresheaf O.obj),
    Functor.map_add (F := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} t)]

/-- `additive_stalkAddCommGroupFunctor` with the source read as `X.Modules` rather than as
`SheafOfModules X.ringCatSheaf`. The two spellings are the same functor, but only the first
exposes the binary biproducts of `X.Modules` to instance search:
`AlgebraicGeometry.Scheme.Modules` is a definition and `HasZeroMorphisms` is not found at the
second spelling at all. -/
theorem additive_stalkAddCommGroupFunctor_modules (X : Scheme.{u}) (x : X) :
    (show X.Modules ⥤ AddCommGrpCat.{u} from
      SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).Additive :=
  ⟨fun {_ _ _ _} => (additive_stalkAddCommGroupFunctor X.ringCatSheaf x).map_add⟩

variable {X : Scheme.{u}} {D : Type*} [Category D] [Preadditive D] (F : X.Modules ⥤ D)
  [F.Additive]

/-- **An additive functor kills a partial biproduct as soon as it kills its summands.** -/
theorem isZero_map_biprodSeries (G : ℕ → X.Modules) :
    ∀ n, (∀ j < n, IsZero (F.obj (G j))) → IsZero (F.obj (Scheme.Modules.biprodSeries G n)) := by
  intro n
  induction n with
  | zero => exact fun _ => Functor.map_isZero F (Scheme.Modules.isZero_biprodSeries_zero G)
  | succ n ih =>
    intro hz
    have hiso : IsIso (F.map (biprod.fst :
        Scheme.Modules.biprodSeries G n ⊞ G n ⟶ Scheme.Modules.biprodSeries G n)) :=
      CategoryTheory.isIso_map_biprod_fst_of_isZero F (hz n (by omega))
    exact IsZero.of_iso (ih fun j hj => hz j (by omega)) (@asIso _ _ _ _ _ hiso)

/-- A functor inverts `f` if it inverts `g` and `f ≫ g`. -/
private theorem isIso_map_of_isIso_map_comp {C E : Type*} [Category C] [Category E] (G : C ⥤ E)
    {A B K : C} (f : A ⟶ B) (g : B ⟶ K) (hg : IsIso (G.map g)) (h : IsIso (G.map (f ≫ g))) :
    IsIso (G.map f) := by
  rw [Functor.map_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hg h

/-- **An additive functor inverts the universal map into a series of biproducts as soon as
exactly one summand survives.** If `F` kills `𝒢ⱼ` for every `j < n` other than `j₀` and inverts
`u_{j₀} : 𝒜 ⟶ 𝒢_{j₀}`, then it inverts
`AlgebraicGeometry.Scheme.Modules.biprodSeriesLift G 𝒜 u n`.

At `n = j₀ + 1` the accumulated biproduct dies, so `F` inverts `biprod.snd` and that identifies
the lift with `u_{j₀}`; above that the new summand dies, so `F` inverts `biprod.fst` and that
identifies the lift with the previous one. -/
theorem isIso_map_biprodSeriesLift (G : ℕ → X.Modules) (A : X.Modules)
    (u : ∀ j, A ⟶ G j) (j₀ : ℕ) (hu : IsIso (F.map (u j₀))) :
    ∀ n, j₀ < n → (∀ j < n, j ≠ j₀ → IsZero (F.obj (G j))) →
      IsIso (F.map (Scheme.Modules.biprodSeriesLift G A u n)) := by
  intro n
  induction n with
  | zero => exact fun h => absurd h (by omega)
  | succ n ih =>
    intro hlt hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
    · refine isIso_map_of_isIso_map_comp F
        (show A ⟶ Scheme.Modules.biprodSeries G n ⊞ G n from
          Scheme.Modules.biprodSeriesLift G A u (n + 1)) biprod.fst
        (CategoryTheory.isIso_map_biprod_fst_of_isZero F (hz n (by omega) (by omega))) ?_
      rw [Scheme.Modules.biprodSeriesLift_comp_biprod_fst]
      exact ih hlt' fun j hj hj₀ => hz j (by omega) hj₀
    · subst heq
      refine isIso_map_of_isIso_map_comp F
        (show A ⟶ Scheme.Modules.biprodSeries G j₀ ⊞ G j₀ from
          Scheme.Modules.biprodSeriesLift G A u (j₀ + 1)) biprod.snd
        (CategoryTheory.isIso_map_biprod_snd_of_isZero F
          (isZero_map_biprodSeries F G j₀ fun j hj => hz j (by omega) (by omega))) ?_
      rwa [Scheme.Modules.biprodSeriesLift_comp_biprod_snd]

end Series

/-! ### The comparison map of a family of closed subschemes, on a stalk -/

section Family

variable {X : Scheme.{u}}

/-- **The comparison map `𝒪_X ⟶ ⊕_{j<N}(iⱼ)_*𝒪_{Zⱼ}` is bijective on the stalk at a point of the
image of exactly one member of the family, provided that member is bijective on local rings.**

At such a point every other summand has vanishing stalk, by [Stacks, Tag 00AE], and the
surviving summand's component of the comparison map is the adjunction unit
`𝒪_X ⟶ (i_{j₀})_*𝒪_{Z_{j₀}}`, whose stalk is the stalk map of `i_{j₀}`. -/
theorem bijective_stalk_pushforwardUnitSeriesMap_of_forall_notMemRange
    {Zs : ℕ → Scheme.{u}} (ι : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (ι j)] (N : ℕ)
    (j₀ : ℕ) (hj₀ : j₀ < N) (z : Zs j₀)
    (hb : Function.Bijective ((ι j₀).stalkMap z))
    (hout : ∀ j < N, j ≠ j₀ → (ι j₀) z ∉ Set.range (ι j).base) :
    Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf ((ι j₀) z)).map
        (Scheme.Modules.pushforwardUnitSeriesMap ι N))) := by
  have := additive_stalkAddCommGroupFunctor_modules X ((ι j₀) z)
  have hu : IsIso ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf ((ι j₀) z)).map
      (_root_.SheafOfModules.unitToPushforwardObjUnit (ι j₀).toRingCatSheafHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_stalk_unitToPushforwardObjUnit (ι j₀) z
        (IsClosedImmersion.isClosedEmbedding (ι j₀)).isInducing hb)
  have hzj : ∀ j < N, j ≠ j₀ →
      IsZero ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf ((ι j₀) z)).obj
        ((Scheme.Modules.pushforward (ι j)).obj
          (_root_.SheafOfModules.unit (Zs j).ringCatSheaf))) :=
    fun j hj hjj =>
      (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf _ _).1
        (isZero_stalkFunctor_pushforward_of_notMemRange (ι j)
          (IsClosedImmersion.isClosedEmbedding (ι j)) _ _ (hout j hj hjj))
  exact (ConcreteCategory.isIso_iff_bijective _).1 (isIso_map_biprodSeriesLift
    (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf ((ι j₀) z))
    (fun j => (Scheme.Modules.pushforward (ι j)).obj
      (_root_.SheafOfModules.unit (Zs j).ringCatSheaf))
    (show X.Modules from _root_.SheafOfModules.unit X.ringCatSheaf)
    (fun j => _root_.SheafOfModules.unitToPushforwardObjUnit (ι j).toRingCatSheafHom) j₀ hu
    N hj₀ hzj)

end Family

/-! ### The family of irreducible components -/

section Components

open Stacks.Topology.Irreducible

variable (X : Scheme.{u}) [IsNoetherian X]

/-- **The irreducible components of a nonempty Noetherian scheme, enumerated by `ℕ`.** There
are finitely many of them ([Stacks, Tag 0BA8]); the first `N` values of the enumeration list
each exactly once, and the remaining values repeat one of them so that every value is a
component. -/
theorem exists_enumeration_irreducibleComponents [Nonempty X] :
    ∃ (N : ℕ) (C : ℕ → Set X), 0 < N ∧ (∀ j, C j ∈ irreducibleComponents X) ∧
      Function.Injective (fun j : Fin N => C j) ∧
      ∀ W ∈ irreducibleComponents X, ∃ j < N, C j = W := by
  classical
  have hfin : Finite {W : Set X // W ∈ irreducibleComponents X} :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin {W : Set X // W ∈ irreducibleComponents X}
  have hNpos : 0 < N := (e ⟨irreducibleComponent (Classical.arbitrary X),
    irreducibleComponent_mem_irreducibleComponents _⟩).pos
  refine ⟨N, fun j => (e.symm ⟨j % N, Nat.mod_lt _ hNpos⟩ : Set X), hNpos,
    fun j => (e.symm ⟨j % N, Nat.mod_lt _ hNpos⟩).2, fun i i' hii => ?_, fun W hW => ?_⟩
  · have h3 : (i : ℕ) % N = (i' : ℕ) % N :=
      congrArg Fin.val (e.symm.injective (Subtype.ext hii))
    rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt, ← Fin.ext_iff] at h3
  · exact ⟨e ⟨W, hW⟩, (e ⟨W, hW⟩).isLt, by simp [Nat.mod_eq_of_lt (e ⟨W, hW⟩).isLt]⟩

/-- **A point lying on only one member of an enumeration of all the irreducible components lies
in that member's `AlgebraicGeometry.Scheme.irreducibleComponentOpen`**, the complement of the
union of the other components. -/
theorem mem_irreducibleComponentOpen_of_mem_disjointLocus {N : ℕ} {C : ℕ → Set X}
    (hCsurj : ∀ W ∈ irreducibleComponents X, ∃ j < N, C j = W) {x : X}
    (hx : x ∈ disjointLocus (fun j : Fin N => C j)) {j₀ : Fin N} (hxj₀ : x ∈ C j₀) :
    x ∈ X.irreducibleComponentOpen (C j₀) := by
  rintro ⟨W, ⟨hW, hWne⟩, hxW⟩
  obtain ⟨j, hj, hjW⟩ := hCsurj W hW
  have hxCj : x ∈ C j := by rwa [hjW]
  refine hx ⟨j, hj⟩ j₀ (fun h => hWne ?_) ⟨hxCj, hxj₀⟩
  rw [Set.mem_singleton_iff, ← hjW]
  exact congrArg C (congrArg Fin.val h)

/-- **[Stacks, Tag 0AYW], paragraph 1: the comparison map `𝒪_X ⟶ ⊕ⱼ (iⱼ)_*𝒪_{Zⱼ}` of the family
of irreducible components is bijective on every stalk away from a finite set of closed points.**

The family is the dévissage's own: `Zⱼ` is the irreducible component `C j` carrying the
subscheme structure of `AlgebraicGeometry.Scheme.irreducibleComponent`, the closed subscheme cut
out by the kernel of the restriction to the complement of the other components. The exceptional
set is the locus where two members meet, which for `topologicalKrullDim X ≤ 1` is a finite set
of closed points, being a closed set that contains no irreducible component — each component
has its generic point off it.

Off that locus a point `x` lies on exactly one component `C j₀`, hence in the open set on which
that component's ideal is the kernel of an **open** immersion; so the stalk map of
`irreducibleComponentι` at `x` is bijective and the other summands have vanishing stalk there.

This is the geometric hypothesis `hbij` of
`AlgebraicGeometry.curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective`, discharged
at the family paragraph 1 of the source actually uses. -/
theorem exists_finite_bijective_stalk_pushforwardUnitSeriesMap_irreducibleComponent
    {N : ℕ} (C : ℕ → Set X) (hC : ∀ j, C j ∈ irreducibleComponents X)
    (hCinj : Function.Injective (fun j : Fin N => C j))
    (hCsurj : ∀ W ∈ irreducibleComponents X, ∃ j < N, C j = W)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ Z : Set X, Z.Finite ∧ (∀ x ∈ Z, IsClosed ({x} : Set X)) ∧
      ∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
        ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
          (Scheme.Modules.pushforwardUnitSeriesMap
            (fun j => X.irreducibleComponentι (C j) (hC j)) N))) := by
  classical
  set Cf : Fin N → Set X := fun j => C j
  have hCfmem : ∀ j, Cf j ∈ irreducibleComponents X := fun j => hC j
  have hCfcl : ∀ j, IsClosed (Cf j) := fun j =>
    isClosed_of_mem_irreducibleComponents _ (hCfmem j)
  have hcl : IsClosed ((disjointLocus Cf)ᶜ) := (isOpen_disjointLocus hCfcl).isClosed_compl
  choose η hη using fun j : Fin N => QuasiSober.sober (hCfmem j).1 (hCfcl j)
  have hnc : ∀ W ∈ irreducibleComponents X, ¬ W ⊆ (disjointLocus Cf)ᶜ := by
    intro W hW hsub
    obtain ⟨j, hj, hjW⟩ := hCsurj W hW
    exact hsub (hjW ▸ (hη ⟨j, hj⟩).mem) (genericPoint_mem_disjointLocus hCfmem hCinj hη ⟨j, hj⟩)
  refine ⟨(disjointLocus Cf)ᶜ,
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hcl hnc,
    fun x hx => Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim hcl hnc hx, fun x hx => ?_⟩
  have hxin : x ∈ disjointLocus Cf := not_not.1 hx
  obtain ⟨j₀, hj₀, hj₀eq⟩ := hCsurj (irreducibleComponent x)
    (irreducibleComponent_mem_irreducibleComponents x)
  have hxj₀ : x ∈ C j₀ := hj₀eq ▸ mem_irreducibleComponent
  obtain ⟨z, rfl, hbz⟩ := exists_bijective_stalkMap_irreducibleComponentι X (C j₀) (hC j₀) x
    (mem_irreducibleComponentOpen_of_mem_disjointLocus X hCsurj hxin
      (j₀ := ⟨j₀, hj₀⟩) hxj₀)
  refine bijective_stalk_pushforwardUnitSeriesMap_of_forall_notMemRange
    (fun j => X.irreducibleComponentι (C j) (hC j)) N j₀ hj₀ z hbz (fun j hj hjne => ?_)
  rw [range_irreducibleComponentι]
  exact fun hmem => hxin ⟨j, hj⟩ ⟨j₀, hj₀⟩ (fun h => hjne (congrArg Fin.val h))
    ⟨hmem, hxj₀⟩

end Components

end AlgebraicGeometry

end
