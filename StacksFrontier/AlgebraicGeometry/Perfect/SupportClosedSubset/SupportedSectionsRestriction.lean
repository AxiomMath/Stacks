module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedSectionsComplexInclusion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction

/-!
# Sections with support restrict to sections with support

Let `X` be a scheme, let `T ⊆ X` be a subset and let `U ⊆ X` be an open subscheme. A section of
an `𝒪_X`-module `ℱ` over an open contained in `U` has the same germs read on `X` and read on `U`,
so it is supported on `T` exactly when it is supported on `U ∩ T`. Hence the subsheaf of
sections supported on `T` restricts to the subsheaf of sections supported on the preimage of `T`:

`(ℋ_T ℱ)|_U ≅ ℋ_{U ∩ T}(ℱ|_U)`,

compatibly with the two inclusions into `ℱ|_U`, and likewise for a complex of `𝒪_X`-modules.

## Main results

* `exists_iso_of_injective_same_range`: two sheaves of modules mapping injectively onto the same
  sections of a third are isomorphic over it.
* `suppSection_restrict_subset_iff`: a section over an open of `U` is supported on the preimage of
  `T` exactly when it is supported on `T`.
* `exists_supportedSectionsRestrictIso`: the comparison at a single module, together with its
  compatibility with the inclusions.
* `exists_complexIso_of_degreewise_of_mono`: degreewise isomorphisms over a third complex with
  monomorphic structure maps assemble into an isomorphism of complexes.
* `exists_supportedSectionsComplexRestrictIso`: the comparison for a complex.

## References

* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 01AT](https://stacks.math.columbia.edu/tag/01AT)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedSectionsRestriction

/-! ### Two subsheaves with the same sections -/

/-- Two sheaves of modules mapping injectively onto the same sections of a third are isomorphic
over it. -/
public theorem exists_iso_of_injective_same_range {X : Scheme.{u}} {A B F : X.Modules}
    (a : A ⟶ F) (b : B ⟶ F)
    (ha : ∀ V, Function.Injective (a.val.app V))
    (hb : ∀ V, Function.Injective (b.val.app V))
    (hab : ∀ V, Set.range (a.val.app V) = Set.range (b.val.app V)) :
    ∃ e : A ≅ B, e.hom ≫ b = a := by
  let e V : A.val.obj V ≃ₗ[X.ringCatSheaf.obj.obj V] B.val.obj V :=
    (LinearEquiv.ofInjective (a.val.app V).hom (ha V)).trans
      ((LinearEquiv.ofEq _ _ (Submodule.ext fun s ↦ Set.ext_iff.mp (hab V) s)).trans
        (LinearEquiv.ofInjective (b.val.app V).hom (hb V)).symm)
  have he V s : b.val.app V (e V s) = a.val.app V s := by
    show ((LinearEquiv.ofInjective (b.val.app V).hom (hb V)) (e V s)).val = _
    simp [e]
  let ee : A.val ≅ B.val := PresheafOfModules.isoMk (fun V ↦ (e V).toModuleIso) (by
    intro V W f
    ext s
    apply hb W
    show b.val.app W (e W (A.val.map f s)) = b.val.app W (B.val.map f (e V s))
    exact (he W (A.val.map f s)).trans ((PresheafOfModules.naturality_apply a.val f s).trans
      ((congrArg (F.val.map f) (he V s)).symm.trans
        (PresheafOfModules.naturality_apply b.val f (e V s)).symm)))
  refine ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso ee, ?_⟩
  ext V s
  exact he (op V) s

/-! ### Supported sections, sectionwise -/

/-- A section is supported on `T` exactly when all its germs outside `T` vanish. -/
public theorem suppSection_subset_iff_germ_eq_zero {X : Scheme.{u}} (T : Set X) (F : X.Modules)
    (V : X.Opens) (s : Γ(F, V)) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).suppSection V s ⊆
        T ∩ (V : Set X) ↔
      ∀ (x : X) (hx : x ∈ V), x ∉ T → F.presheaf.germ V x hx s = 0 := by
  constructor
  · intro h x hx hxT
    by_contra hne
    exact hxT (h ⟨hx, hne⟩).1
  · rintro h x ⟨hxV, hne⟩
    refine ⟨?_, hxV⟩
    by_contra hxT
    exact hne (h x hxV hxT)

/-- A section over an open of `U` is supported on the preimage of `T` exactly when it is
supported on `T`. -/
public theorem suppSection_restrict_subset_iff {X : Scheme.{u}} (T : Set X) (U : X.Opens)
    (F : X.Modules) (V : U.toScheme.Opens)
    (s : Γ((Scheme.Modules.restrictFunctor U.ι).obj F, V)) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
          ((Scheme.Modules.restrictFunctor U.ι).obj F)).suppSection V s ⊆
        (U.ι ⁻¹' T) ∩ (V : Set U.toScheme) ↔
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).suppSection (U.ι ''ᵁ V) s ⊆
        T ∩ (U.ι ''ᵁ V : Set X) := by
  refine Iff.trans (suppSection_subset_iff_germ_eq_zero (U.ι ⁻¹' T)
    ((Scheme.Modules.restrictFunctor U.ι).obj F) V s) ?_
  refine Iff.trans ?_ (suppSection_subset_iff_germ_eq_zero T F (U.ι ''ᵁ V) s).symm
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ hxT
    refine (ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι y F hy) s).symm.trans ?_
    show (Scheme.Modules.restrictStalkNatIso U.ι y).hom.app F
      (((Scheme.Modules.restrictFunctor U.ι).obj F).presheaf.germ V y hy s) = 0
    rw [h y hy hxT]
    exact map_zero _
  · intro h y hy hn
    refine (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.restrictStalkNatIso U.ι y).hom.app F)).1 ?_
    exact ((ConcreteCategory.congr_hom (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι y F
      hy) s).trans (h (U.ι y) ⟨y, hy, rfl⟩ hn)).trans (map_zero _).symm

/-! ### The comparison at a module -/

/-- The subsheaf of sections supported on `T` restricts to the subsheaf of sections supported on
the preimage of `T`, compatibly with the two inclusions into the restriction of the coefficient
module. -/
public theorem exists_supportedSectionsRestrictIso {X : Scheme.{u}} (T : Set X) (U : X.Opens)
    (F : X.Modules) :
    ∃ e : (Scheme.Modules.restrictFunctor U.ι).obj
          (supportedSectionsSheaf T F).1 ≅
        (supportedSectionsSheaf (U.ι ⁻¹' T)
          ((Scheme.Modules.restrictFunctor U.ι).obj F)).1,
      e.hom ≫ supportedSectionsSheafι (U.ι ⁻¹' T)
          ((Scheme.Modules.restrictFunctor U.ι).obj F) =
        (Scheme.Modules.restrictFunctor U.ι).map (supportedSectionsSheafι T F) := by
  refine exists_iso_of_injective_same_range _ _
    (fun V ↦ (supportedSectionsSheaf T F).2.2.1 (op (U.ι ''ᵁ unop V)))
    (fun V ↦ (supportedSectionsSheaf (U.ι ⁻¹' T)
      ((Scheme.Modules.restrictFunctor U.ι).obj F)).2.2.1 V) fun V ↦ ?_
  ext s
  exact ((mem_supportedSectionsSheafι_range_iff T F (op (U.ι ''ᵁ unop V)) s).trans
    (suppSection_restrict_subset_iff T U F (unop V) s).symm).trans
    (mem_supportedSectionsSheafι_range_iff (U.ι ⁻¹' T)
      ((Scheme.Modules.restrictFunctor U.ι).obj F) V s).symm

/-! ### The comparison for a complex -/

/-- Two complexes mapping degreewise into a third, with monomorphic structure maps on one side
and degreewise isomorphisms compatible with them, are isomorphic over that third complex. -/
public theorem exists_complexIso_of_degreewise_of_mono {C : Type*} [Category* C] [Preadditive C]
    {ι : Type*} {cs : ComplexShape ι} {A B K : HomologicalComplex C cs}
    (a : A ⟶ K) (b : B ⟶ K) (hb : ∀ n, Mono (b.f n))
    (e : ∀ n, A.X n ≅ B.X n) (he : ∀ n, (e n).hom ≫ b.f n = a.f n) :
    ∃ E : A ≅ B, E.hom ≫ b = a := by
  have hcomm : ∀ i j, cs.Rel i j → (e i).hom ≫ B.d i j = A.d i j ≫ (e j).hom := by
    intro i j _
    have := hb j
    refine (cancel_mono (b.f j)).1 ?_
    calc ((e i).hom ≫ B.d i j) ≫ b.f j = (e i).hom ≫ b.f i ≫ K.d i j := by
          rw [Category.assoc, b.comm]
      _ = a.f i ≫ K.d i j := by rw [← Category.assoc, he]
      _ = A.d i j ≫ a.f j := a.comm i j
      _ = (A.d i j ≫ (e j).hom) ≫ b.f j := by rw [Category.assoc, he]
  let φ : A ⟶ B := { f := fun n ↦ (e n).hom, comm' := hcomm }
  have hiso : ∀ n, IsIso (φ.f n) := fun n ↦ (e n).isIso_hom
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components _
  exact ⟨asIso φ, HomologicalComplex.hom_ext _ _ he⟩

/-- The subcomplex of sections supported on `T` of a complex of `𝒪_X`-modules restricts to the
subcomplex of sections supported on the preimage of `T`. -/
public theorem exists_supportedSectionsComplexRestrictIso {X : Scheme.{u}} (T : Set X)
    (U : X.Opens) (I : CochainComplex X.Modules ℤ) :
    Nonempty
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((supportedSectionsFunctor X.toRingedSpace T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) ≅
        ((supportedSectionsFunctor U.toScheme.toRingedSpace (U.ι ⁻¹' T)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) := by
  choose e he using fun n : ℤ ↦ exists_supportedSectionsRestrictIso T U (I.X n)
  obtain ⟨E, _⟩ := exists_complexIso_of_degreewise_of_mono
    (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Stacks.Perfect.SupportedSectionsComplex.supportedSectionsComplexι
        X.toRingedSpace T I))
    (Stacks.Perfect.SupportedSectionsComplex.supportedSectionsComplexι
      U.toScheme.toRingedSpace (U.ι ⁻¹' T)
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))
    (fun n ↦ supportedSectionsSheafι_mono (U.ι ⁻¹' T) _) e he
  exact ⟨E⟩

end Stacks.Perfect.SupportedSectionsRestriction

end
