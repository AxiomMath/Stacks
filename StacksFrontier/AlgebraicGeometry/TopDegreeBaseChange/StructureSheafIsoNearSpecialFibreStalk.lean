module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.RelativeAssassinValuationRing
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafSurjectivityBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreLocal

/-!
# The kernel of `𝒪_Y ⟶ f_* 𝒪_X` near the special fibre

Let `f : X ⟶ Y` and `q : Y ⟶ S` be morphisms of schemes and `s ∈ S`. The last paragraph of the
proof of [Stacks, Tag 0E7L] shows that `𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism near `Y_s` once it is
surjective there, `f_* 𝒪_X` is flat over `S` along `Y_s`, the map is injective on the special
fibre, and its kernel is of finite type. This file proves that statement.

## Main results

* `mem_smul_top_of_mono_pullback_fiberι`: a morphism of `𝒪_Y`-modules whose pullback to `Y_s`
  is a monomorphism is injective modulo `𝔪_s` on every stalk at a point of `Y_s`; the stalk of
  the pullback is `𝒪_{Y_s,y'} ⊗ (-)_y` ([Stacks, Tag 0098]) and `𝒪_{Y_s,y'} = 𝒪_{Y,y}/𝔪_s`.
* `mono_pullback_map_unitToPushforwardUnit`: injectivity of `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` on a base
  change gives injectivity of the pullback of `𝒪_Y ⟶ f_* 𝒪_X`.
* `exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isFiniteType_kernel`: the claim.
* `exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isLocallyNoetherian`: the claim over a
  locally Noetherian target, where the kernel is of finite type by [Stacks, Tag 02O5].

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

variable {Y S : Scheme.{u}}

/-- A monomorphism of `𝒪_Y`-modules is injective on the stalk modules of
`Stacks.ModuleSkyscraper.modulesStalkFunctor`. -/
theorem injective_modulesStalkFunctor_map_of_mono {M N : Y.Modules} (ψ : M ⟶ N) [Mono ψ]
    (y : Y) : Function.Injective ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map ψ) :=
  (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap (O := Y.ringCatSheaf) ψ).1
    ‹Mono ψ› y

/-- The stalk at `y` of an `𝒪_Y`-module, as a module over the local ring of `S` at `q y`
through the stalk map of `q`. -/
abbrev baseStalkModule (q : Y ⟶ S) (y : Y) (M : Y.Modules) :
    Module (S.presheaf.stalk (q y))
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj M) :=
  Module.compHom _ (q.stalkMap y).hom

/-- The scalar actions of `𝒪_{S,q y}` (through `baseStalkModule`) and of `𝒪_{Y,y}` on the stalk
at `y` of an `𝒪_Y`-module form a scalar tower. -/
theorem baseStalkModule_isScalarTower (q : Y ⟶ S) (y : Y) (M : Y.Modules) :
    letI := (q.stalkMap y).hom.toAlgebra
    letI := baseStalkModule q y M
    IsScalarTower (S.presheaf.stalk (q y)) (Y.presheaf.stalk y)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj M) := by
  let := (q.stalkMap y).hom.toAlgebra
  let := baseStalkModule q y M
  exact ⟨fun r a m => mul_smul ((q.stalkMap y).hom r) a m⟩

/-- **Injectivity on the special fibre, read on a stalk.** Let `ψ : M ⟶ N` be a morphism of
`𝒪_Y`-modules whose pullback to the fibre `Y_s` of `q : Y ⟶ S` is a monomorphism, and let `y`
be a point of `Y` over `s`. Then `ψ` is injective modulo `𝔪_s` at `y`: an element of `M_y`
whose image lies in `𝔪_s N_y` lies in `𝔪_s M_y`.

The stalk of the pullback at the point `y'` of `Y_s` over `y` is
`𝒪_{Y_s,y'} ⊗_{𝒪_{Y,y}} (-)_y` (Tag 0098, `Stacks.ModuleSkyscraper.pullbackStalkIso`), and
`𝒪_{Y_s,y'}` is `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` (`AlgebraicGeometry.Scheme.Hom.ker_stalkMap_fiberι`). -/
theorem mem_smul_top_of_mono_pullback_fiberι (q : Y ⟶ S) (s : S) {M N : Y.Modules}
    (ψ : M ⟶ N) [Mono ((Scheme.Modules.pullback (q.fiberι s)).map ψ)] (y' : q.fiber s)
    (m : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).obj M) :
    letI := baseStalkModule q (q.fiberι s y') M
    letI := baseStalkModule q (q.fiberι s y') N
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).map ψ m ∈
        maximalIdeal (S.presheaf.stalk (q (q.fiberι s y'))) •
          (⊤ : Submodule (S.presheaf.stalk (q (q.fiberι s y')))
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).obj N)) →
      m ∈ maximalIdeal (S.presheaf.stalk (q (q.fiberι s y'))) •
          (⊤ : Submodule (S.presheaf.stalk (q (q.fiberι s y')))
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).obj M)) := by
  let := (q.stalkMap (q.fiberι s y')).hom.toAlgebra
  let := baseStalkModule q (q.fiberι s y') M
  let := baseStalkModule q (q.fiberι s y') N
  have := baseStalkModule_isScalarTower q (q.fiberι s y') M
  have := baseStalkModule_isScalarTower q (q.fiberι s y') N
  let : Algebra (Y.presheaf.stalk (q.fiberι s y')) ((q.fiber s).presheaf.stalk y') :=
    ((q.fiberι s).stalkMap y').hom.toAlgebra
  have hinj₁ := injective_modulesStalkFunctor_map_of_mono
    ((Scheme.Modules.pullback (q.fiberι s)).map ψ) y'
  have hnat := ((Stacks.ModuleSkyscraper.pullbackStalkIso (q.fiberι s) y').hom.naturality ψ)
  have hinj : Function.Injective
      ((ModuleCat.extendScalars ((q.fiberι s).stalkMap y').hom).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).map ψ)) := by
    have h2 : Function.Injective
        ((Stacks.ModuleSkyscraper.pullbackStalkIso (q.fiberι s) y').hom.app M ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor (q.fiber s) y').map
            ((Scheme.Modules.pullback (q.fiberι s)).map ψ)) :=
      hinj₁.comp (ConcreteCategory.bijective_of_isIso
        ((Stacks.ModuleSkyscraper.pullbackStalkIso (q.fiberι s) y').app M).hom).1
    rw [← Functor.comp_map, ← hnat] at h2
    exact fun a b hab => h2 (by rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      Functor.comp_map, hab])
  exact mem_smul_top_of_injective_baseChange (C := (q.fiber s).presheaf.stalk y')
    ((q.fiberι s).stalkMap_surjective y') _
    (q.ker_stalkMap_fiberι s y')
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (q.fiberι s y')).map ψ).hom hinj m

/-- Exactness of a kernel sequence on stalks: an element of the stalk of `M` killed by `ψ` comes
from the stalk of the kernel. -/
theorem exists_modulesStalkFunctor_map_kernelι {M N : Y.Modules} (ψ : M ⟶ N) (y : Y)
    (a : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj M)
    (ha : (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map ψ a = 0) :
    ∃ k, (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map (kernel.ι ψ) k = a := by
  have hex : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel ψ)
  have h := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (O := Y.ringCatSheaf) _).1 hex y
  exact (ShortComplex.moduleCat_exact_iff _).1 h a ha

/-- **A monomorphism `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` on a base change makes the pullback of
`𝒪_Y ⟶ f_* 𝒪_X` a monomorphism.** The canonical map over `Y'` factors, up to `g^* 𝒪_Y ≅ 𝒪_{Y'}`,
as the pullback of `𝒪_Y ⟶ f_* 𝒪_X` followed by the degree-zero base-change comparison
(`unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap`). -/
theorem mono_pullback_map_unitToPushforwardUnit {X Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Mono (Scheme.Modules.unitToPushforwardUnit (pullback.snd f g))] :
    Mono ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f)) := by
  have : Mono ((Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
      directImageStructureSheafBaseChangeMap f g) := by
    rw [← unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap]
    exact mono_comp _ _
  exact mono_of_mono _ (directImageStructureSheafBaseChangeMap f g)

/-- **The kernel of `𝒪_Y ⟶ f_* 𝒪_X` dies near the special fibre.** Let `f : X ⟶ Y`,
`q : Y ⟶ S` and `s ∈ S`, and suppose the kernel `𝒦` of `𝒪_Y ⟶ f_* 𝒪_X` is of finite type.
Suppose `𝒪_Y ⟶ f_* 𝒪_X` is surjective on the stalks at the points of an open `V₀ ⊇ Y_s`, that
`f_* 𝒪_X` is flat over `S` at every point of `Y_s`, and that the pullback of
`𝒪_Y ⟶ f_* 𝒪_X` to `Y_s` is a monomorphism. Then there is an open `V ⊇ Y_s` on whose points
`𝒪_Y ⟶ f_* 𝒪_X` is bijective on stalks.

This is the claim at the end of the proof of [Stacks, Tag 0E7L]. The support of `𝒦` is closed;
at a point `y` of `Y_s` the stalk map is injective by the local criterion
`injective_of_surjective_of_flat_of_fg_ker` (the source's appeal to [Stacks, Tag 00ME]), so
`y` is not in that support. -/
theorem exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isFiniteType_kernel
    {X : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [hK : (kernel (Scheme.Modules.unitToPushforwardUnit f)).IsFiniteType]
    (V₀ : Y.Opens) (hV₀ : ∀ y : Y, q y = s → y ∈ V₀)
    (hsurj : ∀ y : Y, y ∈ V₀ → Function.Surjective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)))
    (hflat : ∀ y : Y, q y = s →
      IsFlatOverAt q.toLRSHom.toShHom (directImageStructureSheaf f) y)
    [Mono ((Scheme.Modules.pullback (q.fiberι s)).map (Scheme.Modules.unitToPushforwardUnit f))] :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧ ∀ y : Y, y ∈ V → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  set φ := Scheme.Modules.unitToPushforwardUnit f
  set K : Y.Modules := kernel φ with hKdef
  let st := fun y : Y => Stacks.ModuleSkyscraper.modulesStalkFunctor Y y
  have hcomp : ∀ (y : Y) (k : (st y).obj K), (st y).map φ ((st y).map (kernel.ι φ) k) = 0 :=
    fun y k => by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, kernel.condition, Functor.map_zero]
      rfl
  have hker : ∀ y : Y, LinearMap.ker ((st y).map φ).hom =
      LinearMap.range ((st y).map (kernel.ι φ)).hom := fun y => by
    ext a
    refine ⟨fun ha => ?_, fun ⟨k, hk⟩ => ?_⟩
    · exact exists_modulesStalkFunctor_map_kernelι φ _ a ha
    · rw [LinearMap.mem_ker, ← hk]
      exact hcomp _ k
  -- off the support of the kernel, the stalk map is injective
  have hinj_of_notMem : ∀ y : Y, y ∉ SheafOfModules.supp K →
      Function.Injective ((st y).map φ) := by
    intro y hy
    have hz : Subsingleton ((st y).obj K) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp ((notMem_supp_iff_isZero_stalk K y).mp hy)
    rw [← LinearMap.ker_eq_bot (f := ((st y).map φ).hom), hker, eq_bot_iff]
    rintro _ ⟨k, rfl⟩
    rw [Subsingleton.elim k 0, map_zero]
    exact Submodule.zero_mem _
  -- on the special fibre, the stalk of the kernel vanishes
  have hfib : ∀ y : Y, q y = s → y ∉ SheafOfModules.supp K := by
    intro y hy
    obtain ⟨y', rfl⟩ : y ∈ Set.range (q.fiberι s) := by rw [Scheme.Hom.range_fiberι]; exact hy
    let := (q.stalkMap (q.fiberι s y')).hom.toAlgebra
    let := baseStalkModule q (q.fiberι s y') (Scheme.unitModule Y)
    let := baseStalkModule q (q.fiberι s y') (directImageStructureSheaf f)
    have := baseStalkModule_isScalarTower q (q.fiberι s y') (Scheme.unitModule Y)
    have := baseStalkModule_isScalarTower q (q.fiberι s y') (directImageStructureSheaf f)
    have : IsLocalHom (algebraMap (S.presheaf.stalk (q (q.fiberι s y')))
        (Y.presheaf.stalk (q.fiberι s y'))) :=
      inferInstanceAs (IsLocalHom (q.stalkMap (q.fiberι s y')).hom)
    have : Module.Flat (S.presheaf.stalk (q (q.fiberι s y')))
        ((st (q.fiberι s y')).obj (directImageStructureSheaf f)) := hflat _ hy
    have : Module.Finite (Y.presheaf.stalk (q.fiberι s y'))
        ((st (q.fiberι s y')).obj K) :=
      SheafOfModules.finite_stalk Y.sheaf K (q.fiberι s y')
    have hinj := injective_of_surjective_of_flat_of_fg_ker
      ((st (q.fiberι s y')).map φ).hom (hsurj _ (hV₀ _ hy))
      (by rw [hker, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _)
      (mem_smul_top_of_mono_pullback_fiberι q s φ y')
    refine (notMem_supp_iff_isZero_stalk K _).mpr (AddCommGrpCat.isZero_iff_subsingleton.mpr ?_)
    refine ⟨fun k₁ k₂ => injective_modulesStalkFunctor_map_of_mono (kernel.ι φ) _ ?_⟩
    exact hinj ((hcomp _ k₁).trans (hcomp _ k₂).symm)
  refine ⟨V₀ ⊓ ⟨(SheafOfModules.supp K)ᶜ, (SheafOfModules.isClosed_supp K).isOpen_compl⟩,
    fun y hy => ⟨hV₀ y hy, hfib y hy⟩, fun y hy => ⟨hinj_of_notMem y hy.2, hsurj y hy.1⟩⟩

/-- **The same over a locally Noetherian target, for a proper morphism.** There the kernel of
`𝒪_Y ⟶ f_* 𝒪_X` is of finite type because `f_* 𝒪_X` is coherent ([Stacks, Tag 02O5]). -/
theorem exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isLocallyNoetherian
    {X : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (s : S) [IsProper f] [IsLocallyNoetherian Y]
    (V₀ : Y.Opens) (hV₀ : ∀ y : Y, q y = s → y ∈ V₀)
    (hsurj : ∀ y : Y, y ∈ V₀ → Function.Surjective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)))
    (hflat : ∀ y : Y, q y = s →
      IsFlatOverAt q.toLRSHom.toShHom (directImageStructureSheaf f) y)
    [Mono ((Scheme.Modules.pullback (q.fiberι s)).map (Scheme.Modules.unitToPushforwardUnit f))] :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧ ∀ y : Y, y ∈ V → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)) := by
  have : (Scheme.unitModule Y).IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit Y.ringCatSheaf).IsFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Scheme.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  have : (directImageStructureSheaf f).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f (Scheme.unitModule X)
  have : (kernel (Scheme.Modules.unitToPushforwardUnit f)).IsFiniteType :=
    AlgebraicGeometry.CoherentAbelian.isFiniteType_kernel_of_isCoherent _
  exact exists_isOpen_bijective_stalk_unitToPushforwardUnit_of_isFiniteType_kernel f q s
    V₀ hV₀ hsurj hflat

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
