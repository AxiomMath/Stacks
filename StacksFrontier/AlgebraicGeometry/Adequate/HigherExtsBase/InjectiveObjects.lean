module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.AdequateCategory
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Biproducts
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.MonoCriterion
public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep

/-!
# Injective objects among the adequate functors

The injective objects of the category of adequate module-valued functors on the commutative
`A`-algebras are exactly the extensions of scalars `B ↦ B ⊗[A] I` of the pure injective
`A`-modules `I`.

## Main results

* `AdequateFunctor.exists_moduleExtension_iso_of_injective` — an injective adequate functor is a
  direct summand of an extended module, hence is itself an extended module.
* `AdequateFunctor.pureInjective_of_injective_moduleExtension` — if the extension of a module is
  injective among the adequate functors, the module is pure injective.
* `AdequateFunctor.injective_moduleExtension_of_pureInjective` — the converse.
* `AdequateFunctor.injective_iff_moduleExtension_pureInjective` — the resulting
  characterisation, [Stacks, Tag 0708].

## Implementation notes

Extension of scalars is fully faithful, so a morphism between extended modules is the extension
of a unique module map, and extension carries the universally injective module maps exactly onto
the monomorphisms. That is what converts the categorical statements into the module-theoretic
ones: a universally exact sequence of modules extends to a short exact sequence of adequate
functors, and a splitting of an extended map is the extension of a splitting.

The characterisation is stated up to natural isomorphism, so no choice of presentation of an
adequate functor is required.

The source deduces the injectivity of the extension of a pure injective module from enough
injectives in the adequate functors, the last part of [Stacks, Tag 06Z7], obtained there from
the right adjoint to the inclusion of the adequate functors into all module-valued functors.
That route is not taken here, since the embeddings supplying enough injectives are exactly the
embeddings into extensions of pure injective modules, so the deduction would be circular.
Instead the extension problem is solved directly by a pushout: the adequate functors are closed
under finite products and therefore abelian, the pushout of the problem is adequate, and the
kernel presentation of that pushout turns the retraction to be found into a splitting of a
universally injective map of modules.

## References

* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AdequateFunctor

/-- A pure injective module admits a retraction of every universally injective map out of it. -/
private lemma exists_leftInverse_of_pureInjective {A : Type u} [CommRing A]
    {I M : Type (max u v)} [AddCommGroup I] [Module A I] [AddCommGroup M] [Module A M]
    (hI : Module.PureInjective A I) (f : I →ₗ[A] M) (hf : UniversallyInjective f) :
    ∃ r : M →ₗ[A] I, r.comp f = LinearMap.id := by
  obtain ⟨r, hr⟩ :=
    (hI I M _ f (LinearMap.range f).mkQ (Module.injective_of_universallyInjective.{u, v} f hf)
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm hf).2.1 (LinearMap.id : I →ₗ[A] I)
  exact ⟨r, LinearMap.ext (LinearMap.congr_fun hr)⟩

/-- An injective adequate functor is a direct summand of an extended module, hence is itself the
extension of a module: the kernel presentation embeds it into an extended module, injectivity
retracts that embedding, and the resulting idempotent of modules splits. -/
public theorem exists_moduleExtension_iso_of_injective {A : Type u} [CommRing A]
    (F : (adequate.{u, v, max u v w} A).FullSubcategory) (hF : Injective F) :
    ∃ I : ModuleCat.{max u v w} A, Nonempty
      (F ≅ (⟨(moduleExtensionFunctor.{max u v w, v} A).obj I,
        isAdequate_moduleExtension I⟩ : (adequate.{u, v, max u v w} A).FullSubcategory)) := by
  obtain ⟨M, N, d, hd⟩ := F.property
  have he : F.obj ≅ kernel ((moduleExtensionFunctor.{max u v w, v} A).map d) :=
    Classical.choice ((isKernelPresentation_iff F.obj d).mp hd)
  let E : (adequate.{u, v, max u v w} A).FullSubcategory :=
    ⟨(moduleExtensionFunctor.{max u v w, v} A).obj M, isAdequate_moduleExtension M⟩
  let i : F ⟶ E := ObjectProperty.homMk (he.hom ≫ kernel.ι _)
  have : Mono i := by
    apply (adequate.{u, v, max u v w} A).ι.mono_of_mono_map
    simpa [i] using (inferInstance : Mono (he.hom ≫ kernel.ι _))
  let r : E ⟶ F := Injective.factorThru (𝟙 F) i
  have hir : i ≫ r = 𝟙 F := Injective.comp_factorThru (𝟙 F) i
  let i₀ := (adequate.{u, v, max u v w} A).ι.map i
  let r₀ := (adequate.{u, v, max u v w} A).ι.map r
  have hir₀ : i₀ ≫ r₀ = 𝟙 F.obj := by
    simpa [i₀, r₀] using congrArg ((adequate.{u, v, max u v w} A).ι.map) hir
  let e₀ := r₀ ≫ i₀
  have he₀ : e₀ ≫ e₀ = e₀ := by simp [e₀, reassoc_of% hir₀]
  let g : M ⟶ M := moduleHomOfExtensionNatTrans e₀
  have hmap : (moduleExtensionFunctor.{max u v w, v} A).map g = e₀ :=
    (moduleExtension_natTrans_eq_map e₀).symm
  have hgg : g ≫ g = g := by
    have hext : (moduleExtensionFunctor.{max u v w, v} A).map (g ≫ g) =
        (moduleExtensionFunctor.{max u v w, v} A).map g := by
      rw [Functor.map_comp, hmap, he₀]
    simpa only [moduleHomOfExtensionNatTrans_map] using
      congrArg moduleHomOfExtensionNatTrans hext
  obtain ⟨I, j, p, hpj, hjp⟩ : ∃ (I : ModuleCat.{max u v w} A) (j : I ⟶ M) (p : M ⟶ I),
      p ≫ j = g ∧ j ≫ p = 𝟙 I := by
    refine ⟨ModuleCat.of A g.hom.range, ModuleCat.ofHom g.hom.range.subtype,
      ModuleCat.ofHom g.hom.rangeRestrict, by ext; rfl, ?_⟩
    ext x
    change g.hom (x : M) = (x : M)
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgg) y
  let Y : (adequate.{u, v, max u v w} A).FullSubcategory :=
    ⟨(moduleExtensionFunctor.{max u v w, v} A).obj I, isAdequate_moduleExtension I⟩
  let J : Y.obj ⟶ E.obj := (moduleExtensionFunctor.{max u v w, v} A).map j
  let Q : E.obj ⟶ Y.obj := (moduleExtensionFunctor.{max u v w, v} A).map p
  have hQJ : Q ≫ J = e₀ := by rw [← Functor.map_comp, hpj, hmap]
  have hJQ : J ≫ Q = 𝟙 Y.obj := by
    rw [← Functor.map_comp, hjp]
    exact (moduleExtensionFunctor.{max u v w, v} A).map_id I
  let a : Y ⟶ F := ObjectProperty.homMk J ≫ r
  let b : F ⟶ Y := i ≫ ObjectProperty.homMk Q
  have hab : a ≫ b = 𝟙 Y := by
    apply ObjectProperty.hom_ext
    change (J ≫ r.hom) ≫ (i.hom ≫ Q) = 𝟙 Y.obj
    calc
      (J ≫ r.hom) ≫ (i.hom ≫ Q) = J ≫ (r.hom ≫ i.hom) ≫ Q := by simp [Category.assoc]
      _ = J ≫ e₀ ≫ Q := rfl
      _ = J ≫ (Q ≫ J) ≫ Q := by rw [← hQJ]
      _ = (J ≫ Q) ≫ (J ≫ Q) := by simp [Category.assoc]
      _ = 𝟙 Y.obj := by rw [hJQ, Category.id_comp]
  have hba : b ≫ a = 𝟙 F := by
    apply ObjectProperty.hom_ext
    change (i.hom ≫ Q) ≫ (J ≫ r.hom) = 𝟙 F.obj
    calc
      (i.hom ≫ Q) ≫ (J ≫ r.hom) = i.hom ≫ (Q ≫ J) ≫ r.hom := by simp [Category.assoc]
      _ = i.hom ≫ e₀ ≫ r.hom := by rw [hQJ]
      _ = i.hom ≫ (r.hom ≫ i.hom) ≫ r.hom := rfl
      _ = (i.hom ≫ r.hom) ≫ (i.hom ≫ r.hom) := by simp [Category.assoc]
      _ = 𝟙 F.obj := by rw [show i.hom ≫ r.hom = 𝟙 F.obj from hir₀, Category.id_comp]
  exact ⟨I, ⟨⟨b, a, hba, hab⟩⟩⟩

/-- If the extension of an `A`-module is an injective object among the adequate functors, then
the module is pure injective: a universally exact sequence of modules extends to a short exact
sequence of adequate functors, and a lift there is the extension of a lift of modules. -/
public theorem pureInjective_of_injective_moduleExtension {A : Type u} [CommRing A]
    (I : ModuleCat.{max u v w} A)
    (hI : Injective (⟨(moduleExtensionFunctor.{max u v w, v} A).obj I,
      isAdequate_moduleExtension I⟩ : (adequate.{u, v, max u v w} A).FullSubcategory)) :
    Module.PureInjective A I := by
  intro K M N _ _ _ _ _ _ f g hf hg hex hfu
  refine ⟨LinearMap.lcomp_injective_of_surjective g hg, ?_, ?_⟩
  · intro h
    let EK : (adequate.{u, v, max u v w} A).FullSubcategory :=
      ⟨(moduleExtensionFunctor.{max u v w, v} A).obj (ModuleCat.of A K),
        isAdequate_moduleExtension _⟩
    let EM : (adequate.{u, v, max u v w} A).FullSubcategory :=
      ⟨(moduleExtensionFunctor.{max u v w, v} A).obj (ModuleCat.of A M),
        isAdequate_moduleExtension _⟩
    let EI : (adequate.{u, v, max u v w} A).FullSubcategory :=
      ⟨(moduleExtensionFunctor.{max u v w, v} A).obj I, isAdequate_moduleExtension I⟩
    let fm : EK ⟶ EM :=
      ObjectProperty.homMk ((moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom f))
    have hfm : Mono fm := by
      apply (adequate.{u, v, max u v w} A).ι.mono_of_mono_map
      simpa [fm] using
        mono_moduleExtension_map_of_universallyInjective (ModuleCat.ofHom f) hfu
    have : Injective EI := hI
    let gm : EK ⟶ EI :=
      ObjectProperty.homMk ((moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom h))
    let lift : EM ⟶ EI := Injective.factorThru gm fm
    have hlift : fm ≫ lift = gm := Injective.comp_factorThru gm fm
    let r : M →ₗ[A] I := (moduleHomOfExtensionNatTrans lift.hom).hom
    have hrmap : lift.hom = (moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom r) :=
      moduleExtension_natTrans_eq_map lift.hom
    refine ⟨r, ?_⟩
    have hlift' : (moduleExtensionFunctor.{max u v w, v} A).map
          (ModuleCat.ofHom f ≫ ModuleCat.ofHom r) =
        (moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom h) := by
      calc
        _ = fm.hom ≫ lift.hom := by
          rw [Functor.map_comp, ← hrmap]
          rfl
        _ = gm.hom := congrArg (fun z => z.hom) hlift
        _ = _ := rfl
    have hr' : (ModuleCat.ofHom f ≫ ModuleCat.ofHom r) = ModuleCat.ofHom h := by
      simpa only [moduleHomOfExtensionNatTrans_map] using
        congrArg moduleHomOfExtensionNatTrans hlift'
    exact congrArg ModuleCat.Hom.hom hr'
  · exact (LinearMap.exact_iff.mp <|
      LinearMap.exact_lcomp_of_exact_of_surjective I
        (LinearMap.exact_iff.mpr hex.symm) hg).symm

/-- The extension of a pure injective module is an injective object among the adequate functors.
Given an extension problem `g : F ⟶ I̲` along a monomorphism `f : F ⟶ G` of adequate functors,
the pushout of `g` along `f` is again adequate, so it embeds into an extended module; the
composite of `I̲ ⟶ pushout` with that embedding is the extension of a universally injective
module map, which pure injectivity splits, and the splitting retracts the pushout onto `I̲`. -/
public theorem injective_moduleExtension_of_pureInjective {A : Type u} [CommRing A]
    (I : ModuleCat.{max u v w} A) (hI : Module.PureInjective A I) :
    Injective (⟨(moduleExtensionFunctor.{max u v w, v} A).obj I,
      isAdequate_moduleExtension I⟩ : (adequate.{u, v, max u v w} A).FullSubcategory) := by
  let EI : (adequate.{u, v, max u v w} A).FullSubcategory :=
    ⟨(moduleExtensionFunctor.{max u v w, v} A).obj I, isAdequate_moduleExtension I⟩
  refine Injective.mk ?_
  intro F G g f hf
  let P : (adequate.{u, v, max u v w} A).FullSubcategory := pushout f g
  let j : EI ⟶ P := pushout.inr f g
  have hj : Mono j := Abelian.mono_pushout_of_mono_f f g
  obtain ⟨M, N, d, hd⟩ := P.property
  let e : P.obj ≅ kernel ((moduleExtensionFunctor.{max u v w, v} A).map d) :=
    Classical.choice ((isKernelPresentation_iff P.obj d).mp hd)
  let m : P.obj ⟶ (moduleExtensionFunctor.{max u v w, v} A).obj M := e.hom ≫ kernel.ι _
  have hjP : Mono ((adequate.{u, v, max u v w} A).ι.map j) :=
    (adequate.{u, v, max u v w} A).ι.map_mono j
  let k : EI.obj ⟶ (moduleExtensionFunctor.{max u v w, v} A).obj M :=
    (adequate.{u, v, max u v w} A).ι.map j ≫ m
  have hk : Mono k := mono_comp _ _
  let φ : I ⟶ M := moduleHomOfExtensionNatTrans k
  have hkφ : k = (moduleExtensionFunctor.{max u v w, v} A).map φ :=
    moduleExtension_natTrans_eq_map k
  have hmono : Mono ((moduleExtensionFunctor.{max u v w, v} A).map φ) := hkφ ▸ hk
  have hfu : UniversallyInjective φ.hom :=
    universallyInjective_of_mono_moduleExtension_map φ hmono
  obtain ⟨r, hr⟩ := exists_leftInverse_of_pureInjective.{u, max v w} hI φ.hom hfu
  let s : P ⟶ EI := ObjectProperty.homMk
    (m ≫ (moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom r))
  have hsplit : j ≫ s = 𝟙 EI := by
    apply ObjectProperty.hom_ext
    change ((adequate.{u, v, max u v w} A).ι.map j ≫
      m ≫ (moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom r)) = 𝟙 EI.obj
    rw [← Category.assoc]
    change k ≫ (moduleExtensionFunctor.{max u v w, v} A).map (ModuleCat.ofHom r) = 𝟙 EI.obj
    rw [hkφ, ← Functor.map_comp, show φ ≫ ModuleCat.ofHom r = 𝟙 I from ModuleCat.hom_ext hr]
    exact (moduleExtensionFunctor.{max u v w, v} A).map_id I
  refine ⟨pushout.inl f g ≫ s, ?_⟩
  rw [← Category.assoc, pushout.condition, Category.assoc, hsplit, Category.comp_id]

/-- **Stacks Project, Tag 0708.** An adequate module-valued functor is injective exactly when it
is naturally isomorphic to the extension of a pure injective module. -/
@[stacks 0708]
public theorem injective_iff_moduleExtension_pureInjective {A : Type u} [CommRing A]
    (F : (adequate.{u, v, max u v w} A).FullSubcategory) :
    Injective F ↔ ∃ I : ModuleCat.{max u v w} A, Module.PureInjective A I ∧
      Nonempty (F.obj ≅ moduleExtension.{max u v w, v} A I) := by
  constructor
  · intro hF
    obtain ⟨I, ⟨e⟩⟩ := exists_moduleExtension_iso_of_injective.{u, v, w} F hF
    exact ⟨I, pureInjective_of_injective_moduleExtension.{u, v, w} I (Injective.of_iso e hF),
      ⟨(adequate.{u, v, max u v w} A).ι.mapIso e⟩⟩
  · rintro ⟨I, hI, ⟨e⟩⟩
    have hEI := injective_moduleExtension_of_pureInjective.{u, v, w} I hI
    exact Injective.of_iso (ObjectProperty.isoMk _ e).symm hEI

end AdequateFunctor

end
