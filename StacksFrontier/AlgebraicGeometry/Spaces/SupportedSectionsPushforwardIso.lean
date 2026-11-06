module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsModulePushforward

/-!
# The direct image of the supported sections, inside a module identified with the direct image

Let `h : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `T` be a closed subset of the points of `Y`, let `G` be an `𝒪_X`-module and
suppose `h_*G` has been identified with an `𝒪_Y`-module `N` by an isomorphism `α`.  Stacks 085B
identifies, inside `h_*G`, the direct image of the submodule of sections of `G` supported over
`|h|⁻¹T` with the submodule of sections of `h_*G` supported on `T`.  Transporting along `α`
turns that into an identification of the direct image of the supported sections of `G` with the
supported sections of `N`, compatibly with the two inclusions.

That is the shape in which the proof of Stacks 0866 uses Stacks 085B: there `α` is the
base-change isomorphism of Stacks 02KG and `N` is the pullback `pr_Y^*(g_*F)`, so the
identification is needed *after* the base change and not before it.

## Main results

* `AlgebraicGeometry.Space.exists_iso_of_range_eq`: two subobjects of an `𝒪_X`-module whose
  inclusions have the same image on the sections over every étale chart are isomorphic over the
  ambient module.
* `AlgebraicGeometry.Space.sectionSupportedIn_iso` and
  `AlgebraicGeometry.Space.image_setOf_sectionSupportedIn`: an isomorphism of `𝒪_Y`-modules
  preserves and reflects the support condition of Stacks 0859, so it carries the sections
  supported on `T` onto the sections supported on `T`.
* `AlgebraicGeometry.Space.exists_iso_modulePushforward_supportedSectionsSubmodule`: **the
  direct image of the submodule of sections supported over `|h|⁻¹T` is, after `α`, the submodule
  of sections of `N` supported on `T`, compatibly with the inclusions.**

## Implementation notes

The identification of two subobjects from an equality of their images on sections is the only
non-formal step, and it is a diagram chase: the image of one inclusion lies in the image of the
other, so it dies in the cokernel of the other, so it factors through it; the two factorisations
are mutually inverse because the inclusions are monomorphisms.  The factorisation is
`CategoryTheory.ShortComplex.Exact.lift` applied to the short exact sequence of a monomorphism
and its cokernel, and the sections criterion is
`SheafOfModules.exact_val_app_of_shortExact`.

Stacks 085B is used in the spelling of Stacks 03LU,
`AlgebraicGeometry.Space.modulePushforward_supportedSectionsSubmodule_range_eq`.

## References

* [Stacks Project, Tag 085B](https://stacks.math.columbia.edu/tag/085B)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections of a composite -/

section Comp

variable {X : AlgebraicSpaces B S hS}

/-- The image of a composite of morphisms of `𝒪_X`-modules on the sections over a chart is the
image of the image. -/
theorem range_comp_val_app {M N P : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (ψ : N ⟶ P)
    (W : SmallEtale B S hS X.1) :
    Set.range ((φ ≫ ψ).val.app (op W)) =
      ψ.val.app (op W) '' Set.range (φ.val.app (op W)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨φ.val.app (op W) x, ⟨x, rfl⟩, (SheafOfModules.comp_val_app_apply φ ψ (op W) x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, SheafOfModules.comp_val_app_apply φ ψ (op W) x⟩

end Comp

/-! ### Two subobjects with the same sections -/

section Subobjects

variable {X : AlgebraicSpaces B S hS}

/-- The short exact sequence of a monomorphism of `𝒪_X`-modules and its cokernel. -/
private theorem shortExact_monoCokernel {C P : Modules.{u, u} B S hS X.1 X.2} (j : C ⟶ P)
    (hj : Mono j) :
    (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (Abelian.monoIsKernelOfCokernel (f := j) _ (colimit.isColimit _))
  mono_f := hj
  epi_g := inferInstanceAs (Epi (cokernel.π j))

/-- A morphism of `𝒪_X`-modules whose image on the sections over every chart lies in the image
of a monomorphism factors through that monomorphism. -/
private theorem exists_lift_of_range_le {A C P : Modules.{u, u} B S hS X.1 X.2} (i : A ⟶ P)
    (j : C ⟶ P) (hj : Mono j)
    (hr : ∀ W : SmallEtale B S hS X.1,
      Set.range (i.val.app (op W)) ⊆ Set.range (j.val.app (op W))) :
    ∃ u : A ⟶ C, u ≫ j = i := by
  have hSEj := shortExact_monoCokernel B S hS j hj
  have hij : i ≫ cokernel.π j = 0 := by
    ext W x
    exact (SheafOfModules.exact_val_app_of_shortExact hSEj W _).mpr (hr W.unop ⟨x, rfl⟩)
  exact ⟨hSEj.exact.lift i hij, hSEj.exact.lift_f i hij⟩

/-- **Two subobjects of an `𝒪_X`-module whose inclusions have the same image on the sections
over every étale chart are isomorphic over the ambient module.**

Each inclusion factors through the other, because its image dies in the other's cokernel, and
the two factorisations are mutually inverse since the inclusions are monomorphisms. -/
theorem exists_iso_of_range_eq {A C P : Modules.{u, u} B S hS X.1 X.2} (i : A ⟶ P) (hi : Mono i)
    (j : C ⟶ P) (hj : Mono j)
    (hr : ∀ W : SmallEtale B S hS X.1,
      Set.range (i.val.app (op W)) = Set.range (j.val.app (op W))) :
    ∃ e : A ≅ C, e.hom ≫ j = i := by
  obtain ⟨u, hu⟩ := exists_lift_of_range_le B S hS i j hj fun W => (hr W).le
  obtain ⟨v, hv⟩ := exists_lift_of_range_le B S hS j i hi fun W => (hr W).ge
  refine ⟨⟨u, v, ?_, ?_⟩, hu⟩
  · rw [← cancel_mono i, Category.assoc, hv, hu, Category.id_comp]
  · rw [← cancel_mono j, Category.assoc, hu, hv, Category.id_comp]

end Subobjects

/-! ### The support condition under an isomorphism -/

section Support

variable {Y : AlgebraicSpaces B S hS}

/-- The inverse of an isomorphism of `𝒪_Y`-modules undoes it on the sections over a chart. -/
private theorem inv_hom_val_app_apply {M N : Modules.{u, u} B S hS Y.1 Y.2} (α : M ≅ N)
    (W : SmallEtale B S hS Y.1) (x : M.val.obj (op W)) :
    α.inv.val.app (op W) (α.hom.val.app (op W) x) = x := by
  rw [← SheafOfModules.comp_val_app_apply α.hom α.inv (op W) x, α.hom_inv_id]
  rfl

/-- **An isomorphism of `𝒪_Y`-modules preserves and reflects the support condition of
Stacks 0859.** -/
theorem sectionSupportedIn_iso {M N : Modules.{u, u} B S hS Y.1 Y.2} (α : M ≅ N)
    (T : Set (points B S hS Y.1)) (W : SmallEtale B S hS Y.1) (x : M.val.obj (op W)) :
    SectionSupportedIn B S hS Y.1 Y.2 T N W (α.hom.val.app (op W) x) ↔
      SectionSupportedIn B S hS Y.1 Y.2 T M W x := by
  refine ⟨fun hx => ?_, fun hx => sectionSupportedIn_map T α.hom W x hx⟩
  have hinv := sectionSupportedIn_map T α.inv W _ hx
  rwa [inv_hom_val_app_apply B S hS α W x] at hinv

/-- **An isomorphism of `𝒪_Y`-modules carries the sections supported on `T` onto the sections
supported on `T`.** -/
theorem image_setOf_sectionSupportedIn {M N : Modules.{u, u} B S hS Y.1 Y.2} (α : M ≅ N)
    (T : Set (points B S hS Y.1)) (W : SmallEtale B S hS Y.1) :
    α.hom.val.app (op W) ''
        {x : M.val.obj (op W) | SectionSupportedIn B S hS Y.1 Y.2 T M W x} =
      {y : N.val.obj (op W) | SectionSupportedIn B S hS Y.1 Y.2 T N W y} := by
  have hbij : Function.Bijective (α.hom.val.app (op W)) :=
    SheafOfModules.bijective_iso_hom_val_app α (op W)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sectionSupportedIn_map T α.hom W x hx
  · intro hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    exact ⟨x, (sectionSupportedIn_iso B S hS α T W x).mp hy, rfl⟩

end Support

/-! ### The direct image of the supported sections, after an identification -/

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 085B transported along an identification of the direct image, on the sections over
one chart.**  The image of the direct image of the inclusion of the sections supported over
`|h|⁻¹T`, followed by `α`, is the image of the inclusion of the sections of `N` supported on
`T`. -/
theorem range_modulePushforward_supportedSectionsSubmodule_comp (h : X ⟶ Y)
    (T : Set (points B S hS Y.1)) (hT : IsClosed T) (G : Modules.{u, u} B S hS X.1 X.2)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (α : (modulePushforward B S hS h).obj G ≅ N)
    (W : SmallEtale B S hS Y.1) :
    Set.range ((((modulePushforward B S hS h).map (supportedSectionsSubmodule B S hS X.1 X.2
          (pointsMap B S hS X.1 h.hom ⁻¹' T) G).ι) ≫ α.hom).val.app (op W)) =
      Set.range ((supportedSectionsSubmodule B S hS Y.1 Y.2 T N).ι.val.app (op W)) := by
  refine (range_comp_val_app B S hS ((modulePushforward B S hS h).map
    (supportedSectionsSubmodule B S hS X.1 X.2
      (pointsMap B S hS X.1 h.hom ⁻¹' T) G).ι) α.hom W).trans ?_
  refine (congrArg (fun s => α.hom.val.app (op W) '' s)
    (modulePushforward_supportedSectionsSubmodule_range_eq B S hS h T hT G W)).trans ?_
  rw [range_supportedSectionsSubmodule_ι B S hS Y T ((modulePushforward B S hS h).obj G) W,
    range_supportedSectionsSubmodule_ι B S hS Y T N W]
  exact image_setOf_sectionSupportedIn B S hS α T W

/-- **Stacks 085B transported along an identification of the direct image.**  For a closed
subset `T` of the points of `Y`, an `𝒪_X`-module `G` and an isomorphism `α : h_*G ≅ N`, the
direct image of the submodule of sections of `G` supported over `|h|⁻¹T` is, after `α`, the
submodule of sections of `N` supported on `T`, compatibly with the two inclusions. -/
theorem exists_iso_modulePushforward_supportedSectionsSubmodule (h : X ⟶ Y)
    (T : Set (points B S hS Y.1)) (hT : IsClosed T) (G : Modules.{u, u} B S hS X.1 X.2)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (α : (modulePushforward B S hS h).obj G ≅ N) :
    ∃ β : (modulePushforward B S hS h).obj
            (supportedSectionsSubmodule B S hS X.1 X.2
              (pointsMap B S hS X.1 h.hom ⁻¹' T) G).toSheafOfModules ≅
          (supportedSectionsSubmodule B S hS Y.1 Y.2 T N).toSheafOfModules,
      (modulePushforward B S hS h).map (supportedSectionsSubmodule B S hS X.1 X.2
            (pointsMap B S hS X.1 h.hom ⁻¹' T) G).ι ≫ α.hom =
        β.hom ≫ (supportedSectionsSubmodule B S hS Y.1 Y.2 T N).ι := by
  have hmonoι := mono_modulePushforward_map B S hS h (supportedSectionsSubmodule B S hS X.1 X.2
    (pointsMap B S hS X.1 h.hom ⁻¹' T) G).ι inferInstance
  have hmono : Mono ((modulePushforward B S hS h).map (supportedSectionsSubmodule B S hS X.1 X.2
      (pointsMap B S hS X.1 h.hom ⁻¹' T) G).ι ≫ α.hom) :=
    mono_comp' hmonoι (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom α))
  obtain ⟨e, he⟩ := exists_iso_of_range_eq B S hS _ hmono
    (supportedSectionsSubmodule B S hS Y.1 Y.2 T N).ι inferInstance
    (range_modulePushforward_supportedSectionsSubmodule_comp B S hS h T hT G N α)
  exact ⟨e, he.symm⟩

/-- **Stacks 085B transported along an identification of the direct image**, with the subset
upstairs given as a set in its own right together with the identification of it with the inverse
image of the one downstairs. -/
theorem exists_iso_modulePushforward_supportedSectionsSubmodule_of_eq_preimage (h : X ⟶ Y)
    (T : Set (points B S hS Y.1)) (hT : IsClosed T) (T' : Set (points B S hS X.1))
    (hT' : T' = pointsMap B S hS X.1 h.hom ⁻¹' T) (G : Modules.{u, u} B S hS X.1 X.2)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (α : (modulePushforward B S hS h).obj G ≅ N) :
    ∃ β : (modulePushforward B S hS h).obj
            (supportedSectionsSubmodule B S hS X.1 X.2 T' G).toSheafOfModules ≅
          (supportedSectionsSubmodule B S hS Y.1 Y.2 T N).toSheafOfModules,
      (modulePushforward B S hS h).map
            (supportedSectionsSubmodule B S hS X.1 X.2 T' G).ι ≫ α.hom =
        β.hom ≫ (supportedSectionsSubmodule B S hS Y.1 Y.2 T N).ι := by
  subst hT'
  exact exists_iso_modulePushforward_supportedSectionsSubmodule B S hS h T hT G N α

end Pushforward

end AlgebraicGeometry.Space

end
