module

public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectLocalRange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalFamilySubobject

/-!
# Stacks 077Z: the subsheaves cut out by a family assemble into a submodule of the crystal

`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/CrystalFamilySubobject.lean` turns the
restriction half of the compatibility of a family of sections of a crystal `(F, α)` on a system
of schemes into geometry: for each index `i` the spans of the family cut out a quasi-coherent
`κ`-generated subsheaf `G i ⊆ F i`.  This file proves the second half, which is what makes the
family `G` a submodule of the crystal:

```
α φ ((f φ)^* (G i)) = G i'
```

for every transition `φ` with `j φ = (i, i')`.  With that, the exhaustion half of Stacks 077Z
follows from the material already in place, and the tag is complete.

## The shape of the proof

The subsheaf `α φ ((f φ)^* (G i))` is taken as an image subobject, so the assertion is *not* an
equality of the ranges of a single sections map; it is settled locally, by
`Stacks.AlgebraicGeometry.Subsheaf.mk_eq_mk_of_local_range_eq`, over the affine opens `V` of
`X i'` which lie inside the preimage of an affine open `U` of `X i`.  Such opens refine every
neighbourhood of every point of `X i'` and are exactly the opens the family's transition
compatibility speaks about, and over them both sides are computed:

* the sections of `α φ ((f φ)^* (G i))` over `V` are spanned by the transitions of the sections
  of `G i` over `U`, because the pullbacks of the sections over `U` span the sections of the
  pullback over `V` (`AlgebraicGeometry.span_pullbackSection_eq_top`, applied to the
  quasi-coherent `G i`) and the comparison isomorphism is linear on sections;
* the sections of `G i` over `U` are the span of the family there, and the span of the
  transitions of a span is the span of the transitions, by the semilinearity of the transition
  map on sections;
* the sections of `G i'` over `V` are the span of the family there, which the transition
  compatibility identifies with the span of the transitions of the family over `U`.

## Main definitions

* `Stacks.AlgebraicGeometry.Crystals.Crystal.familySubcrystal`: the submodule of the crystal cut
  out by a doubly-compatible family of sections.

## Main results

* `Stacks.AlgebraicGeometry.Crystals.Crystal.transport_familySubobject`: **the subsheaves cut
  out by a doubly-compatible family of sections are matched by the comparison isomorphisms.**
* `Stacks.AlgebraicGeometry.Crystals.Crystal.exists_cardinalGeneratedSubcrystal_mem`: every
  section of the crystal over an affine open of one of the schemes of the system is a section of
  a `cardinalBound D`-generated submodule of the crystal.  This is the exhaustion hypothesis of
  `Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem`.
* `Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone`: **Stacks
  077Z, the colimit assertion**, for the cardinal `cardinalBound D` attached to the system.
  Together with `Stacks.AlgebraicGeometry.Crystals.isFiltered_cardinalGeneratedSubcrystal` this
  is the whole of the tag.

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration

universe u

namespace Stacks.AlgebraicGeometry.Crystals

variable {D : SchemeSystem.{u}}

namespace Crystal

/-! ### The transition map on sections is additive -/

/-- The transition map on sections of a crystal kills the zero section. -/
@[simp]
theorem transitionSection_zero (M : Crystal D) (φ : D.Φ) (U : (D.X (D.j φ).1).Opens)
    (V : (D.X (D.j φ).2).Opens) (h : V ≤ (D.f φ) ⁻¹ᵁ U) :
    M.transitionSection φ U V h 0 = 0 := by
  simp only [transitionSection, map_zero]

/-- The transition map on sections of a crystal is additive. -/
@[simp]
theorem transitionSection_add (M : Crystal D) (φ : D.Φ) (U : (D.X (D.j φ).1).Opens)
    (V : (D.X (D.j φ).2).Opens) (h : V ≤ (D.f φ) ⁻¹ᵁ U) (a b : Γ(M.F (D.j φ).1, U)) :
    M.transitionSection φ U V h (a + b)
      = M.transitionSection φ U V h a + M.transitionSection φ U V h b := by
  simp only [transitionSection, map_add]

/-- **The span of the transitions of a span is the span of the transitions.**  The transition map
on sections is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`
(`Stacks.AlgebraicGeometry.Crystals.Crystal.transitionSection_smul`), so the scalars of the span
upstairs are absorbed into the span downstairs.  This is the crystal-theoretic form of
`Stacks.AlgebraicGeometry.GabberColimit.span_image_span`. -/
theorem span_image_transitionSection_span (M : Crystal D) (φ : D.Φ)
    (U : (D.X (D.j φ).1).Opens) (V : (D.X (D.j φ).2).Opens) (h : V ≤ (D.f φ) ⁻¹ᵁ U)
    (S : Set Γ(M.F (D.j φ).1, U)) :
    Submodule.span Γ(D.X (D.j φ).2, V)
        ((fun a => M.transitionSection φ U V h a) ''
          (Submodule.span Γ(D.X (D.j φ).1, U) S : Set Γ(M.F (D.j φ).1, U)))
      = Submodule.span Γ(D.X (D.j φ).2, V)
        ((fun a => M.transitionSection φ U V h a) '' S) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro y ⟨m, hm, rfl⟩
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    simp only [M.transitionSection_smul]
    exact Submodule.smul_mem _ _ hx

/-! ### The sections of the transported subsheaf over a compatible pair of affine opens -/

/-- **The transition of a section of a subsheaf of `F i`.**  Pulling a section of a subsheaf
`A ⊆ F i` back along `f φ` and pushing it into `F i'` along the pullback of the inclusion
followed by the comparison isomorphism gives the transition of that section read in `F i`. -/
theorem pullbackArrow_app_pullbackSectionHom (M : Crystal D) (φ : D.Φ)
    {A : (D.X (D.j φ).1).Modules} (jA : A ⟶ M.F (D.j φ).1) (U : (D.X (D.j φ).1).Opens)
    (V : (D.X (D.j φ).2).Opens) (h : V ≤ (D.f φ) ⁻¹ᵁ U) (y : Γ(A, U)) :
    ((Scheme.Modules.pullback (D.f φ)).map jA ≫ (M.α φ).hom).app V
        (pullbackSectionHom (D.f φ) A U V h y)
      = M.transitionSection φ U V h (jA.app U y) := by
  have hnat := Scheme.Modules.pullbackSection_naturality (D.f φ) jA U V h y
  rw [transitionSection, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  exact congrArg (fun z => (M.α φ).hom.app V z) hnat

/-- **The sections of the transported subsheaf over a compatible pair of affine opens.**  For a
quasi-coherent subsheaf `A ⊆ F i` and affine opens `U ⊆ X i`, `V ⊆ X i'` with `V ⊆ (f φ)⁻¹ U`,
the sections of `α φ ((f φ)^* A)` over `V` are spanned by the transitions of the sections of `A`
over `U`: the pullbacks of the sections over `U` span the sections of `(f φ)^* A` over `V` by
`AlgebraicGeometry.span_pullbackSection_eq_top`, and the map pushing them into `F i'` is linear
over the functions on `V`. -/
theorem range_pullbackArrow_comp_app (M : Crystal D) (φ : D.Φ)
    {A : (D.X (D.j φ).1).Modules} [A.IsQuasicoherent] (jA : A ⟶ M.F (D.j φ).1)
    {U : (D.X (D.j φ).1).Opens} (hU : IsAffineOpen U) {V : (D.X (D.j φ).2).Opens}
    (hV : IsAffineOpen V) (h : V ≤ (D.f φ) ⁻¹ᵁ U) :
    Set.range (((Scheme.Modules.pullback (D.f φ)).map jA ≫ (M.α φ).hom).app V)
      = (Submodule.span Γ(D.X (D.j φ).2, V)
          ((fun a => M.transitionSection φ U V h a) '' Set.range (jA.app U)) :
            Set Γ(M.F (D.j φ).2, V)) := by
  set a := (Scheme.Modules.pullback (D.f φ)).map jA ≫ (M.α φ).hom
  have htop : Submodule.span Γ(D.X (D.j φ).2, V)
      (Set.range fun y : Γ(A, U) => pullbackSectionHom (D.f φ) A U V h y) = ⊤ :=
    span_pullbackSection_eq_top (D.f φ) A hU hV h
  have himg : (appₗ a V) ''
        (Set.range fun y : Γ(A, U) => pullbackSectionHom (D.f φ) A U V h y)
      = (fun b => M.transitionSection φ U V h b) '' Set.range (jA.app U) := by
    rw [← Set.range_comp, ← Set.range_comp]
    exact congrArg Set.range
      (funext fun y => M.pullbackArrow_app_pullbackSectionHom φ jA U V h y)
  calc Set.range (a.app V) = (LinearMap.range (appₗ a V) : Set Γ(M.F (D.j φ).2, V)) :=
        (LinearMap.coe_range (appₗ a V)).symm
    _ = _ := by rw [LinearMap.range_eq_map, ← htop, Submodule.map_span, himg]

/-! ### The sections of the subsheaf cut out by a family -/

variable (M : Crystal D) (T : M.Family)
  (hc : ∀ i : D.I, GabberColimit.IsCompatible (M.F i) (M.familySubmodule T i))

/-- **The sections of the subsheaf cut out by a family over an affine open** are the span of the
family there, by `Stacks.AlgebraicGeometry.GabberColimit.obj_sheafSubmodule`. -/
theorem range_familySubmoduleHom_app (i : D.I) (W : (D.X i).affineOpens) :
    Set.range ((M.familySubmoduleHom T hc i).app W.1)
      = (Submodule.span Γ(D.X i, W.1) (T ⟨i, W⟩) : Set Γ(M.F i, W.1)) := by
  have : (M.F i).IsQuasicoherent := M.isQuasicoherent i
  show Set.range
    ((GabberColimit.submoduleHom (M.F i) (M.familySubmoduleSheaf T hc i)).app W.1) = _
  refine Set.ext fun s => ?_
  rw [GabberColimit.mem_range_submoduleHom_app,
    show (M.familySubmoduleSheaf T hc i).toSubmodule.obj (op W.1) = M.familySubmodule T i W from
      GabberColimit.obj_sheafSubmodule (M.F i) (M.familySubmodule T i) (hc i) W]
  exact Iff.rfl

/-- The sections over an affine open of the arrow of the subobject cut out by a family are the
span of the family there. -/
theorem range_familySubobject_arrow_app (i : D.I) (W : (D.X i).affineOpens) :
    Set.range ((M.familySubobject T hc i).arrow.app W.1)
      = (Submodule.span Γ(D.X i, W.1) (T ⟨i, W⟩) : Set Γ(M.F i, W.1)) := by
  rw [show M.familySubobject T hc i = Subobject.mk (M.familySubmoduleHom T hc i) from rfl,
    Subsheaf.range_mk_arrow_app]
  exact M.range_familySubmoduleHom_app T hc i W

/-! ### The subsheaves are matched by the comparison isomorphisms -/

/-- **The subsheaves cut out by a doubly-compatible family of sections are matched by the
comparison isomorphisms.**  This is the second compatibility of the family turned into geometry:
together with the quasi-coherence of the subsheaves it says that they form a submodule of the
crystal in the sense of Stacks 077Z.

The assertion is local on `X i'`, by
`Stacks.AlgebraicGeometry.Subsheaf.mk_eq_mk_of_local_range_eq`, and it is checked over the affine
opens contained in the preimage of an affine open of `X i` — the opens the hypothesis `htrans`
speaks about, which refine every neighbourhood of every point because the affine opens of a
scheme form a basis and the preimage of an open is open. -/
theorem transport_familySubobject (M : Crystal D) [D.IsFlat] (T : M.Family)
    (hc : ∀ i, GabberColimit.IsCompatible (M.F i) (M.familySubmodule T i))
    (htrans : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
      (V : (D.X (D.j φ).2).affineOpens) (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1),
      Submodule.span Γ(D.X (D.j φ).2, V.1) (T ⟨(D.j φ).2, V⟩)
        = Submodule.span Γ(D.X (D.j φ).2, V.1)
          ((fun a => M.transitionSection φ U.1 V.1 h a) '' T ⟨(D.j φ).1, U⟩))
    (φ : D.Φ) :
    M.transport φ (M.familySubobject T hc (D.j φ).1) = M.familySubobject T hc (D.j φ).2 := by
  have : ((M.familySubobject T hc (D.j φ).1 : (D.X (D.j φ).1).Modules)).IsQuasicoherent :=
    M.isQuasicoherent_familySubobject T hc (D.j φ).1
  rw [M.transport_eq_mk φ]
  refine Subsheaf.mk_eq_mk_of_local_range_eq _ (M.familySubmoduleHom T hc (D.j φ).2)
    (fun O => ∃ (V : (D.X (D.j φ).2).affineOpens) (U : (D.X (D.j φ).1).affineOpens),
      V.1 = O ∧ V.1 ≤ (D.f φ) ⁻¹ᵁ U.1) ?_ ?_
  · intro O x hx
    obtain ⟨-, ⟨U, hUaff, rfl⟩, hxU, -⟩ :=
      (D.X (D.j φ).1).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((D.f φ).base x)) isOpen_univ
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVle⟩ :=
      (D.X (D.j φ).2).isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((O ⊓ (D.f φ) ⁻¹ᵁ U : (D.X (D.j φ).2).Opens) : Set (D.X (D.j φ).2)) from
          ⟨hx, hxU⟩) (O ⊓ (D.f φ) ⁻¹ᵁ U).isOpen
    have hle : V ≤ O ⊓ (D.f φ) ⁻¹ᵁ U := hVle
    exact ⟨V, hle.trans inf_le_left, hxV,
      ⟨V, hVaff⟩, ⟨U, hUaff⟩, rfl, hle.trans inf_le_right⟩
  · rintro O ⟨V, U, rfl, hVU⟩
    rw [M.range_pullbackArrow_comp_app φ (M.familySubobject T hc (D.j φ).1).arrow U.2 V.2 hVU,
      M.range_familySubobject_arrow_app T hc (D.j φ).1 U,
      M.span_image_transitionSection_span φ U.1 V.1 hVU (T ⟨(D.j φ).1, U⟩),
      M.range_familySubmoduleHom_app T hc (D.j φ).2 V, htrans φ U V hVU]

/-- **The submodule of a crystal cut out by a doubly-compatible family of sections.**  Its
components are the subsheaves of `Stacks.AlgebraicGeometry.Crystals.Crystal.familySubobject`,
quasi-coherent by `isQuasicoherent_familySubobject` and matched by the comparison isomorphisms by
`transport_familySubobject`. -/
def familySubcrystal (M : Crystal D) [D.IsFlat] (T : M.Family)
    (hc : ∀ i, GabberColimit.IsCompatible (M.F i) (M.familySubmodule T i))
    (htrans : ∀ (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
      (V : (D.X (D.j φ).2).affineOpens) (h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1),
      Submodule.span Γ(D.X (D.j φ).2, V.1) (T ⟨(D.j φ).2, V⟩)
        = Submodule.span Γ(D.X (D.j φ).2, V.1)
          ((fun a => M.transitionSection φ U.1 V.1 h a) '' T ⟨(D.j φ).1, U⟩)) :
    Subcrystal M where
  sub i := M.familySubobject T hc i
  isQuasicoherent i := M.isQuasicoherent_familySubobject T hc i
  transport_sub φ := M.transport_familySubobject T hc htrans φ

/-! ### Exhaustion -/

/-- **Every section of a crystal over an affine open of one of the schemes of the system is a
section of a `cardinalBound D`-generated submodule of the crystal.**  The submodule is the one cut
out by the closure of the one-element family consisting of the given section
(`exists_bounded_compatible_family_isLocallyIn`), which is `cardinalBound D`-bounded, cuts out
`cardinalBound D`-generated subsheaves by `isCardinalGenerated_familySubobject`, and contains the
section by `mem_range_familySubobject_arrow_app`.

This is the exhaustion hypothesis of
`Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem`. -/
theorem exists_cardinalGeneratedSubcrystal_mem (M : Crystal D) [D.IsFlat] (i : D.I)
    (U : (D.X i).affineOpens) (s : Γ(M.F i, U.1)) :
    ∃ N : CardinalGeneratedSubcrystal M (cardinalBound D),
      s ∈ Set.range ((N.1.sub i).arrow.app U.1) := by
  obtain ⟨T, hTb, hTres, hTtrans, hs⟩ :=
    M.exists_bounded_compatible_family_isLocallyIn (aleph0_le_cardinalBound D)
      (mk_Phi_le_cardinalBound D) (mk_affineOpens_le_cardinalBound D) i U s
  refine ⟨⟨M.familySubcrystal T (fun i' => M.isCompatible_familySubmodule T hTres i') hTtrans,
    fun i' => M.isCardinalGenerated_familySubobject T _ hTb i'⟩, ?_⟩
  exact M.mem_range_familySubobject_arrow_app T _ i U.1 s hs

end Crystal

/-! ### Stacks 077Z -/

/-- **Stacks 077Z, the colimit assertion.**  For the cardinal `cardinalBound D`, which depends
only on the system of schemes and not on the crystal, every crystal in quasi-coherent modules on
a flat system of schemes is the colimit of its `cardinalBound D`-generated submodules.

Together with `Stacks.AlgebraicGeometry.Crystals.isFiltered_cardinalGeneratedSubcrystal`, which
says that those submodules form a directed system, this is the whole of the tag: there is a
cardinal `κ` such that every object of `CQC(X)` is the directed colimit of its `κ`-generated
submodules. -/
@[stacks 077Z "the colimit"]
def isColimit_cardinalGeneratedSubcrystalCocone (D : SchemeSystem.{u}) [D.IsFlat]
    (M : Crystal D) : IsColimit (cardinalGeneratedSubcrystalCocone M (cardinalBound D)) :=
  isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem M (cardinalBound D)
    (aleph0_le_cardinalBound D) M.exists_cardinalGeneratedSubcrystal_mem

end Stacks.AlgebraicGeometry.Crystals

end
