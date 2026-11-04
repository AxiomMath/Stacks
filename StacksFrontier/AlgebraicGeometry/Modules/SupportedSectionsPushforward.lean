module

public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections

/-!
# Pushforward of the sections supported in a closed subset

Let `f : X ⟶ Y` be a morphism of schemes, `Z` a closed subset of `Y` and `F` a sheaf of
`𝒪_X`-modules. Pushing forward the subsheaf of sections of `F` supported over `f ⁻¹ Z` gives the
subsheaf of `f_* F` of sections supported on `Z`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.range_pushforward_supportedSectionsSubmodule_eq`: the two
  subsheaves have the same sections inside `f_* F`, on every open of `Y`.

## Implementation notes

The equality of subsheaves is expressed as the equality, on every open, of the ranges of their
canonical inclusions into `f_* F`; this records at the same time that the identification is
compatible with those inclusions. Retrocompactness of the complement of `Z`,
quasi-compactness and quasi-separatedness of `f`, and quasi-coherence of `F` play no part — the
statement is a sheaf-theoretic identity. Closedness of `Z` is essential: it is what makes
`U ⊓ Zᶜ` an open on which a section supported on `Z` must vanish.

The germwise criterion is a private lemma, proved in both directions. In the forward direction a
section whose germs vanish off `f ⁻¹ Z` restricts to zero on `f ⁻¹ (U ⊓ Zᶜ)` by the sheaf
section-extensionality property, and that restriction computes the germ of the pushforward
section at a point of `U ⊓ Zᶜ`. In the converse direction a vanishing germ of the pushforward
section at `f x` is realized on some open neighbourhood, whose preimage then witnesses the
vanishing germ of the original section at `x`.

## References

* [Stacks Project, Tag 07ZQ](https://stacks.math.columbia.edu/tag/07ZQ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A section of `F` over `f ⁻¹ U` has all its germs outside `f ⁻¹ Z` zero exactly when the
corresponding section of `f_* F` over `U` has all its germs outside `Z` zero. -/
private lemma supported_on_preimage_iff_pushforward_supported
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : Set Y) (hZ : IsClosed Z)
    (F : X.Modules) (U : Y.Opens) (s : Γ(F, f ⁻¹ᵁ U)) :
    (∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U), x ∉ f.base ⁻¹' Z →
      F.presheaf.germ (f ⁻¹ᵁ U) x hx s = 0) ↔
    (∀ (y : Y) (hy : y ∈ U), y ∉ Z →
      ((Scheme.Modules.pushforward f).obj F).presheaf.germ U y hy
        ((Scheme.Modules.pushforward_obj_obj f F U).symm ▸ s) = 0) := by
  classical
  let V : Y.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hVU : V ≤ U := inf_le_left
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := f.preimage_mono hVU
  let sY : Γ((Scheme.Modules.pushforward f).obj F, U) :=
    (Scheme.Modules.pushforward_obj_obj f F U).symm ▸ s
  have hmap : (Opens.map f.base).map (homOfLE hVU) = homOfLE hpre := Subsingleton.elim _ _
  constructor
  · intro hs y hy hyZ
    have hyV : y ∈ V := ⟨hy, hyZ⟩
    have hzero : F.presheaf.map (homOfLE hpre).op s = 0 := by
      apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
      intro x hx
      have hg' : F.presheaf.germ (f ⁻¹ᵁ V) x hx
          (F.presheaf.map (homOfLE hpre).op s) = 0 := by
        rw [TopCat.Presheaf.germ_res_apply]
        exact hs x (hpre hx) hx.2
      obtain ⟨W, hxW, iW, iW0, heq⟩ :=
        F.presheaf.germ_eq x hx hx (F.presheaf.map (homOfLE hpre).op s) 0
          (by simpa using hg')
      refine ⟨W, ⟨iW.le, ⟨hxW, ?_⟩⟩⟩
      have hI : iW = homOfLE iW.le := Subsingleton.elim _ _
      have hI0 : iW0 = homOfLE iW0.le := Subsingleton.elim _ _
      simpa only [hI, hI0] using heq
    have hzero' : ((Scheme.Modules.pushforward f).obj F).presheaf.map
        (homOfLE hVU).op sY = 0 := by
      simp only [Scheme.Modules.pushforward_obj_presheaf_map,
        Scheme.Modules.pushforward_obj_obj, hmap, sY]
      exact hzero
    rw [← TopCat.Presheaf.germ_res_apply
      ((Scheme.Modules.pushforward f).obj F).presheaf (homOfLE hVU) y hyV, hzero']
    exact map_zero _
  · intro hs x hx hxZ
    let y : Y := f.base x
    change f.base x ∈ U at hx
    change f.base x ∉ Z at hxZ
    have hyU : y ∈ U := by simpa only [y] using hx
    have hyZ : y ∉ Z := by simpa only [y] using hxZ
    have hy0 : ((Scheme.Modules.pushforward f).obj F).presheaf.germ U y hyU sY = 0 := hs y hyU hyZ
    obtain ⟨W, hxW, iWU, iWU0, heq⟩ :=
      ((Scheme.Modules.pushforward f).obj F).presheaf.germ_eq y hyU hyU sY 0
        (hy0.trans (map_zero _).symm)
    have hpreW : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U := f.preimage_mono iWU.le
    have hxpreW : x ∈ f ⁻¹ᵁ W := hxW
    have hres : F.presheaf.map (homOfLE hpreW).op s = 0 := by
      simp only [Scheme.Modules.pushforward_obj_presheaf_map,
        Scheme.Modules.pushforward_obj_obj, sY] at heq
      have hmapW : (Opens.map f.base).map iWU = homOfLE hpreW := Subsingleton.elim _ _
      have hmapW0 : (Opens.map f.base).map iWU0 = homOfLE hpreW := Subsingleton.elim _ _
      rw [hmapW, hmapW0] at heq
      exact heq.trans (map_zero (F.presheaf.map (homOfLE hpreW).op).hom)
    show F.presheaf.germ (f ⁻¹ᵁ U) x hx s = 0
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hpreW) x hxpreW, hres]
    exact map_zero _

/-- The sections of a subsheaf of modules over an open are the range of its inclusion there. -/
private lemma range_sheafSubmodule_inclusion {X : Scheme.{u}} {M : X.Modules}
    (N : M.Submodule) (U : X.Opens) : Set.range (Scheme.Modules.Hom.app N.ι U) =
      {s : Γ(M, U) | s ∈ N.toSubmodule.obj (op U)} := by
  ext s
  constructor
  · rintro ⟨t, ht⟩
    change t.1 = s at ht
    subst s; exact t.2
  · exact fun hs => ⟨⟨s, hs⟩, rfl⟩

/-- The range of the pushforward of the inclusion of a subsheaf, on an open `U`, consists of the
sections of the pushforward whose transport to `f ⁻¹ U` lies in the subsheaf. -/
private lemma range_pushforward_sheafSubmodule_inclusion
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : X.Modules}
    (N : M.Submodule) (U : Y.Opens) :
    Set.range (((Scheme.Modules.pushforward f).map N.ι).app U) =
      {s : Γ((Scheme.Modules.pushforward f).obj M, U) |
        ((Scheme.Modules.pushforward_obj_obj f M U ▸ s : Γ(M, f ⁻¹ᵁ U))) ∈
        N.toSubmodule.obj (op (f ⁻¹ᵁ U))} := by
  classical
  ext s
  constructor
  · rintro ⟨t, ht⟩
    let tX : Γ(N.toSheafOfModules, f ⁻¹ᵁ U) :=
      (Scheme.Modules.pushforward_obj_obj f N.toSheafOfModules U) ▸ t
    let sX : Γ(M, f ⁻¹ᵁ U) := (Scheme.Modules.pushforward_obj_obj f M U) ▸ s
    have hval : Scheme.Modules.Hom.app N.ι (f ⁻¹ᵁ U) tX = sX := by
      with_unfolding_all exact ht
    have hmem : sX ∈ Set.range (Scheme.Modules.Hom.app N.ι (f ⁻¹ᵁ U)) := ⟨tX, hval⟩
    rw [range_sheafSubmodule_inclusion] at hmem
    exact hmem
  · intro hs
    let sX : Γ(M, f ⁻¹ᵁ U) := (Scheme.Modules.pushforward_obj_obj f M U) ▸ s
    let tX : Γ(N.toSheafOfModules, f ⁻¹ᵁ U) := ⟨sX, hs⟩
    let t : Γ((Scheme.Modules.pushforward f).obj N.toSheafOfModules, U) :=
      (Scheme.Modules.pushforward_obj_obj f N.toSheafOfModules U).symm ▸ tX
    refine ⟨t, ?_⟩
    with_unfolding_all exact (show Scheme.Modules.Hom.app N.ι (f ⁻¹ᵁ U) tX = sX from rfl)

/-- The pushforward of the subsheaf supported over `Z` is the subsheaf of
the pushforward supported on `Z`, as subobjects of the pushforward sheaf. -/
@[stacks 07ZQ]
theorem range_pushforward_supportedSectionsSubmodule_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Z : Set Y) (hZ : IsClosed Z) (F : X.Modules) (U : Y.Opens) :
    Set.range (((Scheme.Modules.pushforward f).map
      (supportedSectionsSubmodule (f.base ⁻¹' Z) F).ι).app U) =
      Set.range (((supportedSectionsSubmodule Z
      ((Scheme.Modules.pushforward f).obj F)).ι).val.app (op U)) := by
  let N := supportedSectionsSubmodule (f.base ⁻¹' Z) F
  let P := supportedSectionsSubmodule Z ((Scheme.Modules.pushforward f).obj F)
  have hP : Set.range (P.ι.val.app (op U)) =
      Set.range (Scheme.Modules.Hom.app P.ι U) := by rfl
  rw [range_pushforward_sheafSubmodule_inclusion f N U, hP,
    range_sheafSubmodule_inclusion P U]
  ext s
  show ((Scheme.Modules.pushforward_obj_obj f F U ▸ s : Γ(F, f ⁻¹ᵁ U)) ∈
      N.toSubmodule.obj (op (f ⁻¹ᵁ U))) ↔
    s ∈ P.toSubmodule.obj (op U)
  rw [mem_supportedSectionsSubmodule_iff,
    mem_supportedSectionsSubmodule_iff]
  let sX : Γ(F, f ⁻¹ᵁ U) := (Scheme.Modules.pushforward_obj_obj f F U) ▸ s
  have h := supported_on_preimage_iff_pushforward_supported f Z hZ F U sX
  simp only [sX, Scheme.Modules.presheaf] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.Modules
