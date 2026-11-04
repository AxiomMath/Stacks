module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.UnitSeries
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Support bounds for the comparison map `𝒪_X ⟶ g_*𝒪_{X'}` from stalkwise bijectivity

For a finite family of closed immersions `iⱼ : Zⱼ ⟶ X` consider the canonical comparison map

`φ = ` `AlgebraicGeometry.Scheme.Modules.pushforwardUnitSeriesMap i N` `: 𝒪_X ⟶ g_*𝒪_{X'}`.

If `φ` is bijective on the stalk at every point outside a finite set `Z` of closed points of `X`,
then the supports of `kernel φ` and `cokernel φ` lie in `Z`, a set of Krull dimension at most
zero. Consequently, for `X` proper over a field with `dim X ≤ 1`, whose coherent modules have
finite-dimensional cohomology ([Stacks, Tag 02O6]), and `ℰ` finite locally free of constant rank,
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `supp_kernel_subset_of_injective_stalk`, `supp_cokernel_subset_of_surjective_stalk`: if the
  stalk map of `φ` is injective (resp. surjective) at every point outside `Z`, then the support
  of `kernel φ` (resp. `cokernel φ`) is contained in `Z`.
* `topologicalKrullDim_le_zero_of_finite_of_forall_isClosed`: a finite set of closed points has
  Krull dimension at most zero.
* `curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective`: the degree formula
  `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})` for a finite family, from the bijectivity of the stalk maps
  of `𝒪_X ⟶ g_*𝒪_{X'}` outside a finite set of closed points, given [Stacks, Tag 02O6].
* `isIso_pushforwardUnitSeriesMap_one`, `bijective_stalk_pushforwardUnitSeriesMap_id` and
  `curveDegree_eq_sum_pushforwardUnitSeriesMap_id`: at the one-member family `fun _ => 𝟙 X` the
  comparison map is an isomorphism, and the degree formula holds with `Z = ∅`.
* `stalk_map_surjective_of_epi`: an epimorphism of modules on a scheme is surjective on every
  stalk.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits
open scoped ZeroObject

universe u

/-- **A finite set of closed points has Krull dimension at most zero.** -/
@[ega "0 14.1.12" "dim(X) ≤ 0", ega "0 14.1.9" "sufficiency"]
theorem topologicalKrullDim_le_zero_of_finite_of_forall_isClosed {Y : Type*}
    [TopologicalSpace Y] {S : Set Y} (hfin : S.Finite)
    (hcl : ∀ x ∈ S, IsClosed ({x} : Set Y)) : topologicalKrullDim S ≤ 0 :=
  have : Finite S := hfin.to_subtype
  have : T1Space S := ⟨fun a => by
    have h : ((Subtype.val : S → Y) ⁻¹' {(a : Y)}) = ({a} : Set S) := by
      ext b; simp [Subtype.ext_iff]
    exact h ▸ ((hcl a a.2).preimage continuous_subtype_val)⟩
  topologicalKrullDim_zero_of_discreteTopology S

namespace AddCommGrpCat

/-- **A composite of two injective maps which is zero has zero source.** -/
theorem eq_zero_of_comp_eq_zero_of_injective {A B C : AddCommGrpCat.{u}} (u : A ⟶ B) (v : B ⟶ C)
    (huv : u ≫ v = 0) (hu : Function.Injective (ConcreteCategory.hom u))
    (hv : Function.Injective (ConcreteCategory.hom v)) (a : A) : a = 0 := by
  refine hu (hv ?_)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, huv]
  simp

/-- **A composite of two surjective maps which is zero has zero target.** -/
theorem eq_zero_of_comp_eq_zero_of_surjective {A B C : AddCommGrpCat.{u}} (u : A ⟶ B)
    (v : B ⟶ C) (huv : u ≫ v = 0) (hu : Function.Surjective (ConcreteCategory.hom u))
    (hv : Function.Surjective (ConcreteCategory.hom v)) (c : C) : c = 0 := by
  obtain ⟨b, hb⟩ := hv c
  obtain ⟨a, ha⟩ := hu b
  rw [← hb, ← ha, ← ConcreteCategory.comp_apply, huv]
  simp

end AddCommGrpCat

namespace AlgebraicGeometry

/-! ### Stalks of monomorphisms, epimorphisms and isomorphisms of modules -/

/-- **An epimorphism of modules on a scheme is surjective on every stalk.** -/
theorem stalk_map_surjective_of_epi {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) [Epi g]
    (x : X) :
    Function.Surjective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map g)) := by
  let T : ShortComplex X.Modules := ShortComplex.mk g (0 : B ⟶ B) (by simp)
  have hU := (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf T).mp
    ((T.exact_iff_epi rfl).2 inferInstance) x
  exact (AddCommGrpCat.epi_iff_surjective _).mp <|
    (ShortComplex.exact_iff_epi _
      (Functor.map_zero (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x) _ _)).1 hU

/-- **An isomorphism of modules on a scheme is bijective on every stalk.** -/
theorem bijective_stalk_map_of_isIso {X : Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B) [IsIso φ]
    (x : X) :
    Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map φ)) :=
  have : IsIso ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map φ) :=
    Functor.map_isIso _ φ
  ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩

/-- **The stalk functor carries a zero composite to a zero composite.** -/
theorem stalk_map_comp_eq_zero {X : Scheme.{u}} {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C)
    (huv : u ≫ v = 0) (x : X) :
    (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map u ≫
      (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map v = 0 :=
  ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map_comp u v).symm.trans
    ((congrArg (fun w : A ⟶ C =>
        (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map w) huv).trans
      (Functor.map_zero (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x) _ _))

/-! ### The two support bounds from one pointwise statement -/

/-- **Where the stalk map of `φ` is injective, the kernel of `φ` has no support**: if the stalk
map of `φ` is injective at every point outside `Z`, the support of `kernel φ` lies in `Z`. -/
theorem supp_kernel_subset_of_injective_stalk {X : Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B)
    (Z : Set X)
    (h : ∀ x ∉ Z, Function.Injective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map φ))) :
    _root_.SheafOfModules.supp (kernel φ) ⊆ Z := by
  intro x hx
  by_contra hxZ
  obtain ⟨a, ha⟩ := hx
  exact ha (AddCommGrpCat.eq_zero_of_comp_eq_zero_of_injective _ _
    (stalk_map_comp_eq_zero (kernel.ι φ) φ (kernel.condition φ) x)
    (stalk_map_injective_of_mono (kernel.ι φ) x) (h x hxZ) a)

/-- **Where the stalk map of `φ` is surjective, the cokernel of `φ` has no support**: if the
stalk map of `φ` is surjective at every point outside `Z`, the support of `cokernel φ` lies in
`Z`. -/
theorem supp_cokernel_subset_of_surjective_stalk {X : Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B)
    (Z : Set X)
    (h : ∀ x ∉ Z, Function.Surjective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map φ))) :
    _root_.SheafOfModules.supp (cokernel φ) ⊆ Z := by
  intro x hx
  by_contra hxZ
  obtain ⟨c, hc⟩ := hx
  exact hc (AddCommGrpCat.eq_zero_of_comp_eq_zero_of_surjective _ _
    (stalk_map_comp_eq_zero φ (cokernel.π φ) (cokernel.condition φ) x)
    (h x hxZ) (stalk_map_surjective_of_epi (cokernel.π φ) x) c)

/-! ### The degree formula from stalkwise bijectivity -/

/-- **The degree formula for a finite family, from the stalkwise bijectivity of
`𝒪_X ⟶ g_*𝒪_{X'}` outside a finite set of closed points**:
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (Z : Set X) (hZfin : Z.Finite) (hZcl : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hbij : ∀ x ∉ Z, Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
        (Scheme.Modules.pushforwardUnitSeriesMap i N))))
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_of_supp_subset k f i hX E n N Z
    (topologicalKrullDim_le_zero_of_finite_of_forall_isClosed hZfin hZcl)
    (supp_kernel_subset_of_injective_stalk _ Z fun x hx => (hbij x hx).1)
    (supp_cokernel_subset_of_surjective_stalk _ Z fun x hx => (hbij x hx).2)
    h02O6

/-! ### The one-member family `fun _ => 𝟙 X` -/

/-- **At a one-member family whose unit is invertible the comparison map `𝒪_X ⟶ g_*𝒪_{X'}` is
an isomorphism.** -/
theorem isIso_pushforwardUnitSeriesMap_one {X : Scheme.{u}} {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X)
    (h : IsIso (SheafOfModules.unitToPushforwardObjUnit (i 0).toRingCatSheafHom)) :
    IsIso (Scheme.Modules.pushforwardUnitSeriesMap i 1) := by
  have hz : IsZero (Scheme.Modules.pushforwardUnitSeries i 0) :=
    Scheme.Modules.isZero_biprodSeries_zero _
  have hsndiso : IsIso (biprod.snd :
      Scheme.Modules.pushforwardUnitSeries i 0 ⊞
        (Scheme.Modules.pushforward (i 0)).obj (SheafOfModules.unit (Zs 0).ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (i 0)).obj (SheafOfModules.unit (Zs 0).ringCatSheaf)) :=
    ⟨biprod.inr, by
      refine biprod.hom_ext' _ _ ?_ ?_
      · simp only [← Category.assoc, biprod.inl_snd, zero_comp, Category.comp_id]
        exact hz.eq_of_src _ _
      · simp, biprod.inr_snd⟩
  have hsnd := Scheme.Modules.pushforwardUnitSeriesMap_comp_biprod_snd i 0
  have hcomp : IsIso ((show (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      Scheme.Modules.pushforwardUnitSeries i 0 ⊞
        (Scheme.Modules.pushforward (i 0)).obj (SheafOfModules.unit (Zs 0).ringCatSheaf) from
      Scheme.Modules.pushforwardUnitSeriesMap i 1) ≫ biprod.snd) := by
    rwa [hsnd]
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ biprod.snd hsndiso hcomp

/-- **At the one-member family `fun _ => 𝟙 X` the comparison map is bijective on every
stalk.** -/
theorem bijective_stalk_pushforwardUnitSeriesMap_id (X : Scheme.{u}) (x : X) :
    Function.Bijective (ConcreteCategory.hom
      ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map
        (Scheme.Modules.pushforwardUnitSeriesMap (fun _ : ℕ => 𝟙 X) 1))) :=
  have _h : IsIso (Scheme.Modules.pushforwardUnitSeriesMap (fun _ : ℕ => 𝟙 X) 1) :=
    isIso_pushforwardUnitSeriesMap_one _
      ((Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
        (𝟙 X)).1 inferInstance)
  bijective_stalk_map_of_isIso _ x

/-- **The degree formula at the one-member family `fun _ => 𝟙 X`**: for every `X` proper over a
field and of dimension at most one, the degree of `ℰ` is its degree on the single member of that
family. -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_id
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range 1, @curveDegree k _ ((fun _ : ℕ => X) j)
        ((fun _ : ℕ => 𝟙 X) j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          ((fun _ : ℕ => 𝟙 X) j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback ((fun _ : ℕ => 𝟙 X) j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback ((fun _ : ℕ => 𝟙 X) j) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap_of_stalk_bijective k f (fun _ : ℕ => 𝟙 X) hX E n 1
    ∅ Set.finite_empty (by simp)
    (fun x _ => bijective_stalk_pushforwardUnitSeriesMap_id X x) h02O6

end AlgebraicGeometry

end
