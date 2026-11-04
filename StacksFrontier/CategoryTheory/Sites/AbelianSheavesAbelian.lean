module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
import StacksCore.Tactic.StacksAttribute

/-!
# Abelian sheaves on a site form an abelian category

Let `(C, J)` be a site. The category `Sheaf J AddCommGrpCat` of abelian sheaves on `C` is
abelian, and all of its abelian-category notions are computed explicitly: kernels are formed
in presheaves, cokernels are the sheafifications of the presheaf cokernels, monomorphisms are
the morphisms which are injective on sections, epimorphisms are the locally surjective
morphisms, and exactness of a complex is a local lifting condition on sections.

## Main results

* `kernelObjIso`: the underlying presheaf of `kernel φ` is the kernel of `φ` as a morphism of
  presheaves, compatibly with the two inclusions (`kernelObjIso_hom_ι`).
* `mono_iff_injective`, `mono_iff_presheaf_mono`, `mono_iff_isLocallyInjective`: a morphism of
  abelian sheaves is a monomorphism exactly when it is injective on the sections over every
  object, equivalently when it is a monomorphism of presheaves, equivalently when it is
  injective as a map of sheaves.
* `cokernelSheafifyIso`: the sheafification of the cokernel of `φ` as a morphism of presheaves
  is the cokernel of `φ`.
* `epi_iff_isLocallySurjective`: a morphism of abelian sheaves is an epimorphism exactly when
  it is surjective as a map of sheaves.
* `exact_iff_locallyLiftable`: a complex of abelian sheaves is exact at its middle term exactly
  when every section of that term killed by the second map lifts, along the arrows of some
  covering sieve, through the first map.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace Stacks.AbelianSheaves

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

add_to_stacks 03CN "(1) The category of abelian sheaves on a site is abelian. Mathlib proves
  this for sheaves valued in any abelian category admitting sheafification, by transfer along
  the sheafification adjunction, which is the argument of 03CN (1)."
  CategoryTheory.sheafIsAbelian
add_to_sga "4 II 6.7" "special case" CategoryTheory.sheafIsAbelian
add_to_sga "4 IV 11.1.2" "special case" CategoryTheory.sheafIsAbelian
add_to_sga "4½ Arcata 1.6.3" "more general" CategoryTheory.sheafIsAbelian

section Kernels

variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- **The kernel of a morphism of abelian sheaves is its kernel as a morphism of presheaves.**
The underlying presheaf of `kernel φ` is the presheaf kernel of `φ.hom`; the identification is
compatible with the two canonical inclusions, see `kernelObjIso_hom_ι`. -/
@[stacks 03CN "(2) The kernel of a morphism of abelian sheaves is the kernel of the induced
  morphism of underlying presheaves."]
noncomputable def kernelObjIso : (kernel φ).obj ≅ kernel φ.hom :=
  PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{w}) φ

/-- The identification of the underlying presheaf of `kernel φ` with the presheaf kernel of
`φ.hom` is compatible with the two canonical inclusions. -/
@[reassoc (attr := simp)]
lemma kernelObjIso_hom_ι :
    (kernelObjIso φ).hom ≫ kernel.ι φ.hom = (kernel.ι φ).hom := by
  show (PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{w}) φ).hom ≫ kernel.ι φ.hom =
    (kernel.ι φ).hom
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι φ (sheafToPresheaf J AddCommGrpCat.{w})

end Kernels

section Mono

variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- **A morphism of abelian sheaves is a monomorphism exactly when the induced morphism of
presheaves is one.** -/
@[stacks 03CN "(3) A morphism of abelian sheaves is injective in the sense of Homology, i.e.
  a monomorphism, exactly when it is a monomorphism of presheaves."]
theorem mono_iff_presheaf_mono : Mono φ ↔ Mono φ.hom := by
  constructor
  · intro h
    exact (sheafToPresheaf J AddCommGrpCat.{w}).map_mono φ
  · intro h
    exact (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map h

/-- **A morphism of abelian sheaves is a monomorphism exactly when it is injective on the
sections over every object of the site**, that is, exactly when it is injective as a map of
presheaves. -/
@[stacks 03CN "(3) A morphism of abelian sheaves is injective in the sense of Homology, i.e.
  a monomorphism, exactly when it is injective as a map of presheaves: injective on the
  sections over every object of the site."]
theorem mono_iff_injective : Mono φ ↔ ∀ U : Cᵒᵖ, Function.Injective (φ.hom.app U) := by
  rw [mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app]
  exact forall_congr' fun U => AddCommGrpCat.mono_iff_injective _

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **A morphism of abelian sheaves is a monomorphism exactly when it is injective as a map of
sheaves.** Injectivity of a map of sheaves is Mathlib's
`CategoryTheory.Sheaf.IsLocallyInjective`. -/
@[stacks 03CN "(3) A morphism of abelian sheaves is injective in the sense of Homology, i.e.
  a monomorphism, exactly when it is injective as a map of sheaves."]
theorem mono_iff_isLocallyInjective : Mono φ ↔ Sheaf.IsLocallyInjective φ := by
  rw [Sheaf.isLocallyInjective_iff_injective]
  exact mono_iff_injective φ

end Mono

section Cokernels

variable [HasSheafify J AddCommGrpCat.{w}]
variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- The counit of the sheafification adjunction is natural. -/
lemma map_hom_comp_counit :
    (presheafToSheaf J AddCommGrpCat.{w}).map φ.hom ≫
        (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G =
      (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app F ≫ φ :=
  (sheafificationAdjunction J AddCommGrpCat.{w}).counit.naturality φ

/-- Naturality of the inverse of the counit of the sheafification adjunction. -/
lemma comp_counit_inv :
    φ ≫ (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G)).inv =
      (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app F)).inv ≫
        (presheafToSheaf J AddCommGrpCat.{w}).map φ.hom := by
  rw [Iso.comp_inv_eq, Category.assoc, asIso_hom, map_hom_comp_counit, ← Category.assoc,
    asIso_inv, IsIso.inv_hom_id, Category.id_comp]

/-- The composite of a morphism of abelian sheaves with the projection onto its cokernel
vanishes on underlying presheaves. -/
lemma hom_comp_cokernelπ_hom : φ.hom ≫ (cokernel.π φ).hom = 0 :=
  congrArg (fun t : F ⟶ cokernel φ => t.hom) (cokernel.condition φ)

/-- The factorization of the projection `G ⟶ cokernel φ` through the cokernel of `φ` as a
morphism of presheaves. -/
noncomputable def cokernelDescHom : cokernel φ.hom ⟶ (cokernel φ).obj :=
  cokernel.desc φ.hom (cokernel.π φ).hom (hom_comp_cokernelπ_hom φ)

/-- The comparison morphism from the sheafification of the presheaf cokernel of `φ` to the
cokernel of `φ`. -/
noncomputable def cokernelSheafifyHom :
    (presheafToSheaf J AddCommGrpCat.{w}).obj (cokernel φ.hom) ⟶ cokernel φ :=
  (presheafToSheaf J AddCommGrpCat.{w}).map (cokernelDescHom φ) ≫
    (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app (cokernel φ)

/-- Sheafifying the presheaf projection onto the cokernel and comparing with the cokernel of
`φ` recovers the projection onto the cokernel of `φ`. -/
lemma map_cokernelπ_comp_cokernelSheafifyHom :
    (presheafToSheaf J AddCommGrpCat.{w}).map (cokernel.π φ.hom) ≫ cokernelSheafifyHom φ =
      (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G ≫ cokernel.π φ := by
  rw [cokernelSheafifyHom, ← Category.assoc, ← Functor.map_comp, cokernelDescHom,
    cokernel.π_desc]
  exact map_hom_comp_counit (cokernel.π φ)

/-- The composite of `φ` with the sheafified presheaf cokernel projection vanishes. -/
lemma comp_counitInv_comp_map_cokernelπ :
    φ ≫ (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G)).inv ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map (cokernel.π φ.hom) = 0 := by
  rw [← Category.assoc, comp_counit_inv, Category.assoc, ← Functor.map_comp,
    cokernel.condition, Functor.map_zero, Limits.comp_zero]

/-- The morphism from the cokernel of `φ` to the sheafification of the presheaf cokernel of
`φ`, inverse to `cokernelSheafifyHom`. -/
noncomputable def cokernelSheafifyInv :
    cokernel φ ⟶ (presheafToSheaf J AddCommGrpCat.{w}).obj (cokernel φ.hom) :=
  cokernel.desc φ ((asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G)).inv ≫
    (presheafToSheaf J AddCommGrpCat.{w}).map (cokernel.π φ.hom))
    (comp_counitInv_comp_map_cokernelπ φ)

/-- **The cokernel of a morphism of abelian sheaves is the sheafification of its cokernel as a
morphism of presheaves.** -/
@[stacks 03CN "(4) The cokernel of a morphism of abelian sheaves is the sheafification of the
  cokernel of the induced morphism of underlying presheaves."]
noncomputable def cokernelSheafifyIso :
    (presheafToSheaf J AddCommGrpCat.{w}).obj (cokernel φ.hom) ≅ cokernel φ := by
  have hπ : cokernel.π φ ≫ cokernelSheafifyInv φ =
      (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app G)).inv ≫
        (presheafToSheaf J AddCommGrpCat.{w}).map (cokernel.π φ.hom) :=
    cokernel.π_desc _ _ (comp_counitInv_comp_map_cokernelπ φ)
  refine ⟨cokernelSheafifyHom φ, cokernelSheafifyInv φ, ?_, ?_⟩
  · refine (cancel_epi ((presheafToSheaf J AddCommGrpCat.{w}).map (cokernel.π φ.hom))).1 ?_
    rw [Category.comp_id, ← Category.assoc, map_cokernelπ_comp_cokernelSheafifyHom,
      Category.assoc, hπ, ← Category.assoc, asIso_inv, IsIso.hom_inv_id, Category.id_comp]
  · refine (cancel_epi (cokernel.π φ)).1 ?_
    rw [Category.comp_id, ← Category.assoc, hπ, Category.assoc,
      map_cokernelπ_comp_cokernelSheafifyHom, ← Category.assoc, asIso_inv, IsIso.inv_hom_id,
      Category.id_comp]

/-- The forward map of `cokernelSheafifyIso φ` is `cokernelSheafifyHom φ`. -/
@[simp]
lemma cokernelSheafifyIso_hom : (cokernelSheafifyIso φ).hom = cokernelSheafifyHom φ := rfl

end Cokernels

section Epi

variable [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- **A morphism of abelian sheaves is an epimorphism exactly when it is surjective as a map
of sheaves**, i.e. locally surjective: every section of the target is, on the members of some
covering, in the image. -/
@[stacks 03CN "(5) A morphism of abelian sheaves is surjective in the sense of Homology, i.e.
  an epimorphism, exactly when it is surjective as a map of sheaves."]
theorem epi_iff_isLocallySurjective : Epi φ ↔ Sheaf.IsLocallySurjective φ :=
  (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} φ).symm

end Epi

section Exactness

/-- Morphisms of abelian sheaves commute with restriction of sections. -/
private theorem restrict_app_apply {A B : Sheaf J AddCommGrpCat.{w}} (f : A ⟶ B) {U V : C}
    (g : V ⟶ U) (z : A.obj.obj (op U)) :
    B.obj.map g.op (f.hom.app (op U) z) = f.hom.app (op V) (A.obj.map g.op z) :=
  (ConcreteCategory.congr_hom (f.hom.naturality g.op) z).symm

/-- Evaluating an equality of composites of morphisms of abelian sheaves on a section. -/
private theorem app_apply_eq_of_comp_eq {A B E : Sheaf J AddCommGrpCat.{w}} {f : A ⟶ B}
    {g : B ⟶ E} {h : A ⟶ E} (w : f ≫ g = h) (U : Cᵒᵖ) (x : A.obj.obj U) :
    g.hom.app U (f.hom.app U x) = h.hom.app U x :=
  ConcreteCategory.congr_hom (congrArg (fun t : A ⟶ E => t.hom.app U) w) x

/-- If a section of the middle term of a complex of abelian sheaves is, on a covering, in the
image of the first map, then the second map kills it. -/
theorem app_eq_zero_of_imageSieve_mem
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] {A B E : Sheaf J AddCommGrpCat.{w}}
    (d : A ⟶ B) (e : B ⟶ E) (hde : d ≫ e = 0) (U : C) (z : B.obj.obj (op U))
    (hz : Presheaf.imageSieve d.hom z ∈ J U) : e.hom.app (op U) z = 0 := by
  have hE := (isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj E).property
  apply (hE.isSeparated _ hz).ext
  intro V g hg
  obtain ⟨b, hb⟩ := hg
  show E.obj.map g.op (e.hom.app (op U) z) = E.obj.map g.op 0
  rw [map_zero, restrict_app_apply, ← hb]
  exact app_apply_eq_of_comp_eq hde (op V) b

variable [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- A section of the middle term of an exact short complex of abelian sheaves which is killed
by the second map is, on a covering, in the image of the first map. -/
theorem imageSieve_mem_of_exact (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.Exact) (U : C) (z : S.X₂.obj.obj (op U))
    (hz : S.g.hom.app (op U) z = 0) :
    Presheaf.imageSieve S.f.hom z ∈ J U := by
  let Γ := (sheafSections J AddCommGrpCat.{w}).obj (op U)
  have hadd : Γ.Additive := ⟨rfl⟩
  have hlim : PreservesLimitsOfShape WalkingParallelPair Γ := by
    show PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation _ _).obj (op U))
    infer_instance
  let Q := ShortComplex.mk (Γ.map S.iCycles) (Γ.map S.g)
    (by rw [← Γ.map_comp, S.iCycles_g, Γ.map_zero])
  have hQ : Q.Exact := Q.exact_of_f_is_kernel
    (KernelFork.mapIsLimit _ S.cyclesIsKernel Γ)
  obtain ⟨c, hc⟩ := (Q.ab_exact_iff.1 hQ) z hz
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} S.toCycles).2 inferInstance
  apply J.superset_covering (S := Presheaf.imageSieve S.toCycles.hom c)
    ?_ (Presheaf.imageSieve_mem J S.toCycles.hom c)
  intro V g hg
  obtain ⟨b, hb⟩ := hg
  refine ⟨b, ?_⟩
  have hc' : S.iCycles.hom.app (op U) c = z := hc
  rw [← hc', restrict_app_apply, ← hb]
  exact (app_apply_eq_of_comp_eq S.toCycles_i (op V) b).symm

/-- **Exactness of a short complex of abelian sheaves is a local condition.** If every section
of the middle term killed by the second map lifts, along the arrows of some covering sieve,
through the first map, then the complex is exact. -/
theorem exact_of_locallyLiftable (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (h : ∀ ⦃V : C⦄ (z : S.X₂.obj.obj (op V)), S.g.hom.app (op V) z = 0 →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (p : W ⟶ V), T p →
        ∃ x : S.X₁.obj.obj (op W), S.f.hom.app (op W) x = S.X₂.obj.map p.op z) :
    S.Exact := by
  rw [S.exact_iff_epi_kernel_lift, epi_iff_isLocallySurjective]
  refine ⟨fun {V} y => ?_⟩
  have hz : S.g.hom.app (op V) ((kernel.ι S.g).hom.app (op V) y) = 0 := by
    exact app_apply_eq_of_comp_eq (kernel.condition S.g) (op V) y
  obtain ⟨T, hT, hlift⟩ := h ((kernel.ι S.g).hom.app (op V) y) hz
  refine J.superset_covering (fun W p hp => ?_) hT
  obtain ⟨x, hx⟩ := hlift p hp
  refine ⟨x, (mono_iff_injective (kernel.ι S.g)).1 inferInstance (op W) ?_⟩
  have h₁ : (kernel.ι S.g).hom.app (op W) ((kernel.lift S.g S.f S.zero).hom.app (op W) x)
      = S.f.hom.app (op W) x :=
    app_apply_eq_of_comp_eq (kernel.lift_ι S.g S.f S.zero) (op W) x
  have h₂ : (kernel.ι S.g).hom.app (op W) ((kernel S.g).obj.map p.op y)
      = S.X₂.obj.map p.op ((kernel.ι S.g).hom.app (op V) y) :=
    (restrict_app_apply (kernel.ι S.g) p y).symm
  rw [h₁, h₂, hx]

/-- **A complex of abelian sheaves is exact at its middle term exactly when the sections of
that term killed by the second map lift locally through the first map.** -/
@[stacks 03CN "(6) A complex of abelian sheaves is exact at the middle term if and only if,
  for every object of the site and every section of the middle term over it mapping to zero,
  there is a covering of that object on which the section is in the image of the first map."]
theorem exact_iff_locallyLiftable (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) :
    S.Exact ↔ ∀ ⦃V : C⦄ (z : S.X₂.obj.obj (op V)), S.g.hom.app (op V) z = 0 →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (p : W ⟶ V), T p →
        ∃ x : S.X₁.obj.obj (op W), S.f.hom.app (op W) x = S.X₂.obj.map p.op z :=
  ⟨fun hS _ z hz => ⟨Presheaf.imageSieve S.f.hom z,
    imageSieve_mem_of_exact S hS _ z hz, fun _ _ hp => hp⟩,
    exact_of_locallyLiftable S⟩

end Exactness

end Stacks.AbelianSheaves
