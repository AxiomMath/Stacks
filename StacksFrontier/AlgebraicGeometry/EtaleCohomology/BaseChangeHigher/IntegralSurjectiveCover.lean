module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

/-!
# Higher direct images and an integral surjective cover of the base of the sheaf

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer, as in the condition
`BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F04] fixes `q ≥ 1`, assumes
`BC(f, n, q - 1)`, and considers the two commutative diagrams

```
X  ←--  X'  ←-h-  Y  ←-π'-  Y'            X'  ←----h' = π' ≫ h----  Y'
|f      |f'       |e        |e'    and    |f'                       |e'
S  ←--  S'  ←-g-  T  ←-π-   T'            S'  ←----g' = π ≫ g-----  T'
```

in which every square of the first is cartesian, `g` is quasi-compact and quasi-separated, `π`
is integral surjective, and the second diagram is the first one with its two right-hand squares
pasted. For an abelian sheaf `F` on the small étale site of `T` annihilated by `n`, put
`F' = π⁻¹F`. The source asserts that if the base change map
`(f')⁻¹ R^q g'_* F' ⟶ R^q h'_* (e')⁻¹ F'` of the pasted diagram is an isomorphism, then so is
the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the middle square.

The source's proof has two halves. The first is a genuine use of [Stacks, Tag 0F03]: the unit
`F ⟶ π_*π⁻¹F` is injective because `π` is surjective, so part (1) of that tag makes the base
change map of `F` injective and part (2) puts its cokernel inside the cokernel of the base
change map of `π_*F'`; if the latter is an isomorphism its cokernel vanishes, hence so does the
first, and an injective morphism with vanishing cokernel is an isomorphism. That half is proved
here from the tag's own hypotheses, including the injectivity of the unit, which is established
by the stalk argument the source indicates. The second half identifies the base change map of
`π_*F'` with the base change map of `F'` for the pasted diagram, using that `Rπ_* = π_*` for an
integral `π` and the relative Leray spectral sequence; those identifications are hypotheses
here, exactly as in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/
IntegralBase.lean` for the neighbouring [Stacks, Tag 0F05]. See **What is assumed**.

Degrees are indexed as in [Stacks, Tag 0F03] as formalized in this library: the running index is
`q : ℕ`, the hypothesis is `BC(f, n, q)`, and the conclusion is about degree `q + 1`. That is
the source's `q ≥ 1` together with its `BC(f, n, q - 1)`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.EtaleCohomology.isIso_of_geometricStalkAb_family`,
  `Stacks.EtaleCohomology.isZero_of_geometricStalkAb_family`,
  `Stacks.EtaleCohomology.mono_of_geometricStalkAb_family` — a covering family of geometric
  points detects isomorphisms, zero objects and monomorphisms of abelian sheaves on a small
  étale site. The first is the family form of
  `Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb`; the third follows because
  the stalk functors are exact, so they preserve kernels.
* `Stacks.EtaleCohomology.mono_smallEtaleStalkAb_map_unit` — the stalk of the unit
  `F ⟶ π_*π⁻¹F` at a geometric point of `T` of the form `x ≫ π` is injective, by the triangle
  identity of the adjunction and the identification of the stalk of an inverse image.
* `Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective` — **for a surjective `π` the
  unit `F ⟶ π_*π⁻¹F` on abelian sheaves is a monomorphism**, which is the step the source's
  proof opens with. This is the abelian counterpart of
  `Stacks.EtaleCohomology.mono_smallEtaleUnit_of_surjective`, which is for sheaves of sets.
* `Stacks.EtaleCohomology.zsmul_eq_zero_of_additive` — annihilation by `n` passes through any
  additive functor of abelian sheaves, so `π_*π⁻¹F` is annihilated by `n` when `F` is.
* `Stacks.Cohomology.BaseChange.isIso_of_mono_of_isIso_of_mono_cokernelMap` — the purely
  categorical end of the argument: a monomorphism whose cokernel embeds into the cokernel of an
  isomorphism is an isomorphism.
* **[Stacks, Tag 0F04]** itself is not stated here: it is
  `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_integralSurjective`, in
  `IntegralDirectImagePasting.lean`, which is proved from the lemmas above.

## Implementation notes

The three cartesian squares of the first diagram are transcribed as `IsPullback` hypotheses; the
pasted diagram is not a separate hypothesis, being `sq₃.paste_horiz sq₂`. Quasi-compactness and
quasi-separatedness of `g` and integrality and surjectivity of `π` are instance hypotheses,
matching the spelling of `Stacks.EtaleCohomology.BaseChangeHolds`. Annihilation of `F` by `n` is
imposed on every section, again as in `BaseChangeHolds`.

The short exact sequences that part (1) and part (2) of [Stacks, Tag 0F03] need are not visible
here: they are constructed inside
`Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_annihilated` and
`Stacks.EtaleCohomology.mono_cokernelMap_higherBaseChangeMapAb_app_of_annihilated` from the
annihilation hypotheses alone.

Integrality of `π` is transcribed although the proofs here do not consume it: it is a hypothesis
of the source statement, and the source consumes it only through the relative Leray
identifications, which are assumed below. Surjectivity of `π`, by contrast, is consumed, being
what makes the unit `F ⟶ π_*π⁻¹F` a monomorphism.

`Stacks.EtaleCohomology.mono_of_geometricStalkAb_family` is stated for a family rather than for
all geometric points because only the geometric points of `T` which lift to `T'` are reachable:
the stalk of the unit is controlled at `x ≫ π` for `x` a geometric point of `T'`, and
surjectivity of `π` says exactly that those cover `T`.

## What is assumed

Four hypotheses of the main theorem stand in for identifications the source cites or elides.
Each is an identification of functors or a commuting square of morphisms, and none asserts that
a base change map at the index of the conclusion is invertible, so none is a piece of the
conclusion. They are the same four as for [Stacks, Tag 0F05] in `IntegralBase.lean`, at the
present diagram.

* `h0EYP`, the identification `e⁻¹π_* ≅ π'_*(e')⁻¹` for the cartesian square `Y' = Y ×_T T'`.
  This is [Stacks, Tag 0EYP], that direct image along an integral morphism commutes with base
  change, in the abelian small-étale setting. That tag is not
  formalized in this library — `StacksFrontier/AlgebraicGeometry/EtaleCohomology/
  IntegralPushforwardBaseChange.lean` names it in its references and tags nothing with it — so
  the hypothesis is shaped as the natural isomorphism of functors it provides.
* `hLerayBottom` and `hLerayTop`, the relative Leray identifications
  `R^{q+1}(π ≫ g)_* ≅ π_* ⋙ R^{q+1}g_*`-style comparisons for `g' = π ≫ g` and for
  `h' = π' ≫ h`, which hold because direct image along an integral morphism is exact, by
  [Stacks, Tag 04C2], so that `Rπ_* = π_*`. The relative Leray spectral sequence itself
  is [Stacks, Tag 0734]; this library has 0734 only for sheaves of modules
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/RelativeLeraySpectralSequence.lean`),
  not for abelian sheaves on small étale sites.
* `hPaste`, compatibility of the base change maps of [Stacks, Tag 0F02] with those three
  identifications: the base change map of the pasted diagram is the base change map of the
  middle square at `π_*F'`, read through them. This is the horizontal pasting of the derived
  base change comparison, which the source elides and which carries no tag;
  `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean` has
  `mate`, `derived` and `derived_fac`, but no pasting lemma.

## References

* [Stacks Project, Tag 0F04](https://stacks.math.columbia.edu/tag/0F04)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

/-- **A monomorphism whose cokernel embeds into the cokernel of an isomorphism is an
isomorphism.** This is the categorical end of the proof of [Stacks, Tag 0F04]: part (1) of
[Stacks, Tag 0F03] makes `φ` a monomorphism, part (2) embeds `Coker φ` in `Coker ψ`, and `ψ` is
an isomorphism by assumption, so `Coker ψ` and with it `Coker φ` vanish and `φ` is also an
epimorphism. -/
public theorem isIso_of_mono_of_isIso_of_mono_cokernelMap {A : Type*} [Category* A] [Abelian A]
    {F₁ F₂ G₁ G₂ : A} (φ : F₁ ⟶ F₂) (ψ : G₁ ⟶ G₂) {α : F₁ ⟶ G₁} {β : F₂ ⟶ G₂}
    {comm : φ ≫ β = α ≫ ψ} (hφ : Mono φ) (hψ : IsIso ψ)
    (hcoker : Mono (cokernel.map φ ψ α β comm)) : IsIso φ := by
  have := hφ
  have := hψ
  have hzero : IsZero (cokernel ψ) :=
    (Preadditive.epi_iff_isZero_cokernel ψ).1 inferInstance
  have := hcoker
  have : Epi φ :=
    (Preadditive.epi_iff_isZero_cokernel φ).2
      (IsZero.of_mono (cokernel.map φ ψ α β comm) hzero)
  exact isIso_of_mono_of_epi φ

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

/-- Forgetting the group structure of an abelian group commutes with `u`-filtered colimits, the
abelian groups living one universe up. The same instance as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/StalkwiseCriterion.lean`, which
is private there. -/
private instance : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget Ab.{u + 1})

/-! ### Covering families of geometric points detect isomorphisms, zero objects, monomorphisms -/

section Detect

variable {X : Scheme.{u}} {ι : Type u} {Ω : ι → Type u}
  [∀ t, Field (Ω t)] [∀ t, IsSepClosed (Ω t)]

/-- **A covering family of geometric points detects isomorphisms of abelian étale sheaves.** A
morphism of abelian sheaves on the small étale site of `X` is an isomorphism as soon as its map
on the stalk at every member of a family of geometric points whose images cover `X` is one.

This is the family form of
`Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb`, proved the same way: the
morphism is composed with the forgetful functor to sheaves of sets, where a jointly surjective
family of points detects isomorphisms, and the forgetful functor commutes with taking fibres at
a point of a site and reflects isomorphisms. -/
@[sga "4½ Arcata 2.3.2" "partial"]
public theorem isIso_of_geometricStalkAb_family
    (x : ∀ t, Spec (.of (Ω t)) ⟶ X) (hx : ⋃ t, Set.range (x t) = Set.univ)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : ∀ t, IsIso ((smallEtaleStalkAb (x t)).map φ)) : IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (sheafCompose (smallEtaleTopology X) (forget Ab.{u + 1}))]
  refine isIso_of_geometricStalk_family.{0, u} x hx _ fun t ↦ ?_
  have hiso : IsIso ((smallEtaleStalkAb (x t)).map φ) := hφ t
  refine (NatIso.isIso_map_iff
    ((pointSmallEtale (x t)).sheafFiberCompIso (forget Ab.{u + 1})) φ).2 ?_
  exact inferInstanceAs (IsIso ((forget Ab.{u + 1}).map ((smallEtaleStalkAb (x t)).map φ)))

/-- **A covering family of geometric points detects the zero sheaf.** An abelian sheaf on the
small étale site of `X` whose stalk vanishes at every member of a family of geometric points
whose images cover `X` is zero: its zero endomorphism is then an isomorphism on every stalk of
the family, hence an isomorphism, hence equal to the identity. -/
public theorem isZero_of_geometricStalkAb_family
    (x : ∀ t, Spec (.of (Ω t)) ⟶ X) (hx : ⋃ t, Set.range (x t) = Set.univ)
    {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : ∀ t, IsZero ((smallEtaleStalkAb (x t)).obj F)) : IsZero F := by
  have hiso : IsIso (0 : F ⟶ F) := by
    refine isIso_of_geometricStalkAb_family x hx _ fun t ↦ ?_
    have h0 : (0 : (smallEtaleStalkAb (x t)).obj F ⟶ (smallEtaleStalkAb (x t)).obj F) = 𝟙 _ :=
      (hF t).eq_of_src _ _
    rw [Functor.map_zero, h0]
    infer_instance
  refine (IsZero.iff_id_eq_zero F).2 ?_
  rw [← IsIso.hom_inv_id (0 : F ⟶ F), zero_comp]

/-- **A covering family of geometric points detects monomorphisms of abelian étale sheaves.** A
morphism of abelian sheaves on the small étale site of `X` is a monomorphism as soon as its map
on the stalk at every member of a family of geometric points whose images cover `X` is one.

A morphism of an abelian category is a monomorphism exactly when its kernel vanishes; the stalk
functors are exact, so they take the kernel of the morphism to the kernel of its stalk, which
vanishes by hypothesis. -/
public theorem mono_of_geometricStalkAb_family
    (x : ∀ t, Spec (.of (Ω t)) ⟶ X) (hx : ⋃ t, Set.range (x t) = Set.univ)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : ∀ t, Mono ((smallEtaleStalkAb (x t)).map φ)) : Mono φ := by
  rw [Preadditive.mono_iff_isZero_kernel]
  refine isZero_of_geometricStalkAb_family x hx fun t ↦ ?_
  have := hφ t
  exact (isZero_kernel_of_mono ((smallEtaleStalkAb (x t)).map φ)).of_iso
    (PreservesKernel.iso (smallEtaleStalkAb (x t)) φ)

end Detect

/-! ### The unit of the adjunction for a surjective morphism -/

/-- **The stalk of the unit `F ⟶ π_*π⁻¹F` at a geometric point lifting to the source is
injective.** For `π : T' ⟶ T` and a geometric point `x` of `T'`, the stalk at the geometric
point `x ≫ π` of `T` of the unit of the inverse-image/direct-image adjunction on abelian
sheaves is a monomorphism.

The stalk at `x ≫ π` of an abelian sheaf on `T` is the stalk at `x` of its inverse image
(`Stacks.EtaleCohomology.smallEtalePullbackStalkAbIso`), and the inverse image of the unit is
split by the counit, by the triangle identity of the adjunction. -/
public theorem mono_smallEtaleStalkAb_map_unit {T' T : Scheme.{u}} (π : T' ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ T')
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    Mono ((smallEtaleStalkAb (x ≫ π)).map ((smallEtaleAdjunctionAb π).unit.app F)) := by
  have htri : (smallEtalePullbackAb π ⋙ smallEtaleStalkAb x).map
        ((smallEtaleAdjunctionAb π).unit.app F) ≫
      (smallEtaleStalkAb x).map
        ((smallEtaleAdjunctionAb π).counit.app ((smallEtalePullbackAb π).obj F)) = 𝟙 _ := by
    rw [Functor.comp_map, ← Functor.map_comp,
      (smallEtaleAdjunctionAb π).left_triangle_components F]
    exact CategoryTheory.Functor.map_id _ _
  have hfac : (smallEtaleStalkAb (x ≫ π)).map ((smallEtaleAdjunctionAb π).unit.app F) ≫
      ((smallEtalePullbackStalkAbIso π x).inv.app
          ((smallEtalePullbackAb π ⋙ smallEtalePushforwardAb π).obj F) ≫
        (smallEtaleStalkAb x).map
          ((smallEtaleAdjunctionAb π).counit.app ((smallEtalePullbackAb π).obj F))) =
      (smallEtalePullbackStalkAbIso π x).inv.app F := by
    rw [← Category.assoc,
      (smallEtalePullbackStalkAbIso π x).inv.naturality
        ((smallEtaleAdjunctionAb π).unit.app F),
      Category.assoc, htri]
    exact Category.comp_id _
  exact mono_of_mono_fac hfac

/-- **For a surjective morphism the unit `F ⟶ π_*π⁻¹F` on abelian étale sheaves is a
monomorphism.** This is the step the proof of [Stacks, Tag 0F04] opens with, and the abelian
counterpart of `Stacks.EtaleCohomology.mono_smallEtaleUnit_of_surjective`, which is for sheaves
of sets.

The geometric points of `T'` indexed by its points, taking at each the algebraic closure of the
residue field, have images covering `T'`, hence their images under `π` cover `T` because `π` is
surjective; at each of them the stalk of the unit is injective by
`Stacks.EtaleCohomology.mono_smallEtaleStalkAb_map_unit`. -/
public theorem mono_smallEtaleUnitAb_of_surjective {T' T : Scheme.{u}} (π : T' ⟶ T)
    [Surjective π] (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    Mono ((smallEtaleAdjunctionAb π).unit.app F) := by
  refine mono_of_geometricStalkAb_family
    (fun y : T' ↦ T'.algClosedPointHom y ≫ π) ?_ _ fun y ↦ ?_
  · ext t
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := π.surjective t
    refine ⟨y, default, ?_⟩
    rw [Scheme.Hom.comp_apply, algClosedPointHom_apply]
    exact hy
  · exact mono_smallEtaleStalkAb_map_unit π _ F

/-! ### Annihilation by `n` passes through an additive functor -/

/-- **An additive functor of abelian sheaves preserves annihilation by `n`.** If every section
of `F` is annihilated by `n`, then so is every section of `Φ.obj F`: annihilation by `n` says
that `n • 𝟙` vanishes (`Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff`), and an additive
functor takes `n • 𝟙 F` to `n • 𝟙 (Φ.obj F)`. -/
public theorem zsmul_eq_zero_of_additive {C : Type*} [Category* C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (Φ : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}) [Φ.Additive]
    (F : Sheaf J Ab.{u + 1}) (n : ℤ)
    (hF : ∀ (U : Cᵒᵖ) (y : ToType (F.obj.obj U)), n • y = 0) :
    ∀ (V : Dᵒᵖ) (z : ToType ((Φ.obj F).obj.obj V)), n • z = 0 := by
  refine (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff (Φ.obj F) n).1 ?_
  have h : n • 𝟙 F = 0 := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F n).2 hF
  calc n • 𝟙 (Φ.obj F) = Φ.map (n • 𝟙 F) := by
        rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
    _ = 0 := by rw [h, Functor.map_zero]

/-! ### Stacks 0F04 -/

end Stacks.EtaleCohomology

end
