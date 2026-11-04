module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# Finite locally free morphisms are Zariski local on the target

Finite local freeness of a morphism of schemes can be checked on the members of an open cover
of the target. The content splits into two halves: finite local freeness of a *sheaf of
modules* is local on the base, and the direct image `f_* 𝒪_X` is compatible with restriction
to an open of the target.

## Main definitions

* `Stacks.Modules.restrictFreeIso` identifies the restriction of a free sheaf of modules along
  an open immersion with the free sheaf on the same index type.
* `Stacks.Morphisms.pushforwardStructureSheafRestrictIso` identifies the restriction of
  `f_* 𝒪_X` to an open `V` of the target with the direct image of the structure sheaf along
  `f ∣_ V`.
* `Stacks.Morphisms.pushforwardIsoRestrictInv` identifies pushforward along an isomorphism of
  schemes with restriction along its inverse.

## Main results

* `Stacks.Modules.isFiniteLocallyFree_restrict`: the restriction of a finite locally free sheaf
  of modules along an open immersion is finite locally free.
* `Stacks.Modules.isFiniteLocallyFree_of_iSup_eq_top` and
  `Stacks.Modules.isFiniteLocallyFree_of_openCover`: a sheaf of modules whose restrictions to
  the members of an open cover are finite locally free is finite locally free, for a cover by
  open subschemes and for a cover by open immersions respectively.
* `Stacks.Modules.isFiniteLocallyFree_localGenerators_of_iSup_eq_top` is the same statement in
  the local-generators form of Stacks Tag 01C6.
* `Stacks.Morphisms.isFiniteLocallyFree_iff_pointwise` restates
  `Stacks.Morphisms.IsFiniteLocallyFree` using the trivialising-restrictions form of finite local
  freeness.

## Implementation notes

The locality statements are stated in the trivialising-restrictions form
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree` — "every point has an open neighbourhood
on which the module restricts to a free sheaf" — rather than in the `LocalGeneratorsData` form
of Stacks Tag 01C6, because that form is manifestly local. The two agree by
`Stacks.Modules.isFiniteLocallyFree_iff_localGenerators`.

`MorphismProperty.RespectsIso` and `AlgebraicGeometry.IsZariskiLocalAtTarget` for
`AlgebraicGeometry.IsAffineHom` are **not** found by instance search even though Mathlib
declares `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`: the affine target
property is an `outParam` and unification of it against the goal fails. They are therefore
supplied here as terms by `@`-application.

Zariski locality is strictly weaker than Stacks Tag 02VO, which asserts locality for the fpqc
topology.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

/-- The restriction of a free sheaf of modules along an open immersion is the free sheaf of
modules on the same index type. Restriction is a left adjoint, so it preserves the coproduct of
copies of the structure sheaf which defines a free sheaf, and it carries the structure sheaf to
the structure sheaf by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
noncomputable def restrictFreeIso {T S : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    (I : Type u) :
    (restrictFunctor g).obj (SheafOfModules.free (R := S.ringCatSheaf) I) ≅
      SheafOfModules.free (R := T.ringCatSheaf) I :=
  letI F := restrictFunctor g
  letI h : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I h
    (Scheme.Modules.restrictUnitIso g).symm).symm

/-- A trivialisation of `M` along an open immersion `g` restricts to a trivialisation along
`h ≫ g`, for any further open immersion `h`. -/
noncomputable def restrictIsoFreeComp {T' T S : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S)
    [IsOpenImmersion h] [IsOpenImmersion g] (M : S.Modules) (I : Type u)
    (e : (restrictFunctor g).obj M ≅ SheafOfModules.free (R := T.ringCatSheaf) I) :
    (restrictFunctor (h ≫ g)).obj M ≅ SheafOfModules.free (R := T'.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctorComp h g).app M ≪≫ (restrictFunctor h).mapIso e ≪≫
    restrictFreeIso h I

/-- A trivialisation of `M` along an open immersion `g` transfers to any open immersion `g'`
whose topological image is contained in that of `g`. -/
theorem nonempty_restrictIsoFree_of_range_subset {T T' S : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ S)
    [IsOpenImmersion g] [IsOpenImmersion g'] (M : S.Modules) (I : Type u)
    (hr : Set.range g'.base ⊆ Set.range g.base)
    (e : (restrictFunctor g).obj M ≅ SheafOfModules.free (R := T.ringCatSheaf) I) :
    Nonempty ((restrictFunctor g').obj M ≅ SheafOfModules.free (R := T'.ringCatSheaf) I) := by
  have hk : IsOpenImmersion.lift g g' hr ≫ g = g' := IsOpenImmersion.lift_fac g g' hr
  have h1 : IsOpenImmersion (IsOpenImmersion.lift g g' hr ≫ g) := by rw [hk]; infer_instance
  have h2 : IsOpenImmersion (IsOpenImmersion.lift g g' hr) := IsOpenImmersion.of_comp _ g
  exact ⟨(Scheme.Modules.restrictFunctorCongr hk).symm.app M ≪≫
    restrictIsoFreeComp (IsOpenImmersion.lift g g' hr) g M I e⟩

/-- Finite local freeness of a sheaf of modules only depends on its isomorphism class. -/
theorem isFiniteLocallyFree_of_iso {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (hM : Scheme.Modules.IsFiniteLocallyFree M) :
    Scheme.Modules.IsFiniteLocallyFree N := by
  intro x
  obtain ⟨U, hU, I, hIfin, ⟨g⟩⟩ := hM x
  exact ⟨U, hU, I, hIfin, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ g⟩⟩

/-- The restriction of a finite locally free sheaf of modules along an open immersion is finite
locally free. -/
theorem isFiniteLocallyFree_restrict {T S : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    (M : S.Modules) (hM : Scheme.Modules.IsFiniteLocallyFree M) :
    Scheme.Modules.IsFiniteLocallyFree ((restrictFunctor g).obj M) := by
  intro t
  obtain ⟨W, hW, I, hIfin, ⟨e⟩⟩ := hM (g.base t)
  refine ⟨g ⁻¹ᵁ W, hW, I, hIfin, ?_⟩
  have hr : Set.range ((g ⁻¹ᵁ W).ι ≫ g).base ⊆ Set.range W.ι.base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨g.base y.1, y.2⟩, rfl⟩
  obtain ⟨e'⟩ := nonempty_restrictIsoFree_of_range_subset W.ι ((g ⁻¹ᵁ W).ι ≫ g) M I hr e
  exact ⟨((Scheme.Modules.restrictFunctorComp (g ⁻¹ᵁ W).ι g).app M).symm ≪≫ e'⟩

/-- A trivialisation of the restriction of `M` to an open `V` of `T`, along an open immersion
`g : T ⟶ S`, gives one of the restriction of `M` to the image `g ''ᵁ V`. -/
private theorem nonempty_restrictIsoFree_image {T S : Scheme.{u}} (g : T ⟶ S)
    [IsOpenImmersion g] (M : S.Modules) (I : Type u) (V : T.Opens)
    (e : (restrictFunctor V.ι).obj ((restrictFunctor g).obj M) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) I) :
    Nonempty ((restrictFunctor (g ''ᵁ V).ι).obj M ≅
      SheafOfModules.free (R := (g ''ᵁ V).toScheme.ringCatSheaf) I) :=
  nonempty_restrictIsoFree_of_range_subset (V.ι ≫ g) (g ''ᵁ V).ι M I
    (by simp [Scheme.Opens.range_ι, Set.range_comp])
    ((Scheme.Modules.restrictFunctorComp V.ι g).app M ≪≫ e)

/-- Finite local freeness of a sheaf of modules is local on an open cover of the base: a sheaf
of modules whose restrictions to the members of an open cover are finite locally free is finite
locally free. -/
theorem isFiniteLocallyFree_of_openCover {S : Scheme.{u}} (M : S.Modules) (𝒰 : S.OpenCover)
    (h : ∀ i, Scheme.Modules.IsFiniteLocallyFree ((restrictFunctor (𝒰.f i)).obj M)) :
    Scheme.Modules.IsFiniteLocallyFree M := by
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  obtain ⟨V, hV, I, hIfin, ⟨e⟩⟩ := h i y
  exact ⟨𝒰.f i ''ᵁ V, ⟨y, hV, rfl⟩, I, hIfin, nonempty_restrictIsoFree_image (𝒰.f i) M I V e⟩

/-- Finite local freeness of a sheaf of modules is local on the base: a sheaf of modules whose
restrictions to the members `U i` of a cover of the base by open subschemes are finite locally
free is finite locally free. -/
theorem isFiniteLocallyFree_of_iSup_eq_top {S : Scheme.{u}} (M : S.Modules) {ι : Type*}
    (U : ι → S.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, Scheme.Modules.IsFiniteLocallyFree ((restrictFunctor (U i).ι).obj M)) :
    Scheme.Modules.IsFiniteLocallyFree M := by
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  rw [Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨V, hV, I, hIfin, ⟨e⟩⟩ := h i ⟨x, hi⟩
  exact ⟨(U i).ι ''ᵁ V, ⟨⟨x, hi⟩, hV, rfl⟩, I, hIfin,
    nonempty_restrictIsoFree_image (U i).ι M I V e⟩

/-- **Finite local freeness in the local-generators form of Stacks Tag 01C6 is local on the
base.** A sheaf of modules whose restriction to each member of an open cover of the base carries
local generators data which is a finite local free basis carries such data on the whole base. -/
theorem isFiniteLocallyFree_localGenerators_of_iSup_eq_top {S : Scheme.{u}} (M : S.Modules)
    {ι : Type*} (U : ι → S.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((restrictFunctor (U i).ι).obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  (isFiniteLocallyFree_iff_localGenerators M).mp
    (isFiniteLocallyFree_of_iSup_eq_top M U hU fun i =>
      (isFiniteLocallyFree_iff_localGenerators _).mpr (h i))

end Stacks.Modules

namespace Stacks.Morphisms

/-- Pushing a sheaf of modules forward along an isomorphism of schemes is restricting it along
the inverse isomorphism. -/
noncomputable def pushforwardIsoRestrictInv {Y Z : Scheme.{u}} (w : Y ≅ Z) :
    Scheme.Modules.pushforward w.hom ≅ restrictFunctor w.inv :=
  Stacks.Modules.pushforwardIsoPullbackInv w ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback w.inv).symm

/-- The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf of the target. -/
noncomputable def pushforwardStructureSheafIsoUnit {Y Z : Scheme.{u}} (w : Y ≅ Z) :
    pushforwardStructureSheaf w.hom ≅ SheafOfModules.unit Z.ringCatSheaf :=
  (pushforwardIsoRestrictInv w).app _ ≪≫ Scheme.Modules.restrictUnitIso w.inv

/-- **The direct image of the structure sheaf is compatible with restriction to an open of the
target.** Restricting `f_* 𝒪_X` to `V` gives the direct image of the structure sheaf along the
restricted morphism `f ∣_ V`, because restricting `𝒪_X` to `f ⁻¹ᵁ V` gives the structure sheaf
of that open subscheme. -/
noncomputable def pushforwardStructureSheafRestrictIso {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) :
    (restrictFunctor V.ι).obj (pushforwardStructureSheaf f) ≅
      pushforwardStructureSheaf (f ∣_ V) :=
  (Stacks.Modules.pushforwardRestrictFunctorIso f V).app _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ V)).mapIso (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ V).ι)

/-- Finite local freeness of a morphism, stated with the trivialising-restrictions form of
finite local freeness of `f_* 𝒪_X`. -/
theorem isFiniteLocallyFree_iff_pointwise {X S : Scheme.{u}} (f : X ⟶ S) :
    IsFiniteLocallyFree f ↔
      IsAffineHom f ∧ Scheme.Modules.IsFiniteLocallyFree (pushforwardStructureSheaf f) := by
  rw [isFiniteLocallyFree_iff, ← Stacks.Modules.isFiniteLocallyFree_iff_localGenerators]

/-- `AlgebraicGeometry.IsAffineHom` is Zariski local at the target. -/
theorem isAffineHom_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine

/-- `AlgebraicGeometry.IsAffineHom` respects isomorphisms. -/
private theorem isAffineHom_respectsIso :
    MorphismProperty.RespectsIso (@IsAffineHom : MorphismProperty Scheme.{u}) :=
  isAffineHom_isZariskiLocalAtTarget.toRespects

end Stacks.Morphisms

end
