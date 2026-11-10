module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementOpenCohomology

/-!
# Excision for derived sections over an open

Let `Y` be a scheme, let `V` and `W` be opens with `V ∪ W = Y`, and let `G` be a sheaf of modules
on `Y` with no nonzero sections over any open contained in `W`. Then restriction
`H^p(Y, G) ⟶ H^p(V, G)` is an isomorphism for every `p`, cohomology being the right derived
functors of sections. This is how the cohomology of a sheaf supported on a closed subset is
computed on any open neighbourhood of that subset; Stacks 0EG4 uses it to identify
`H^s(V, F/IⁿF)` with `H^s(U, F/IⁿF)` for the opens `V ⊆ U` containing `U ∩ V(I)`.

## Main definitions

* `Stacks.LocalCohomology.sectionsOnOpenRestriction` — the restriction maps between the sections
  functors over two opens of a ringed space, linear over the global functions.
* `Stacks.LocalCohomology.complementOpenRestriction` — the same over `A`, on the complement
  `Spec A ∖ V(a)`.
* `Stacks.LocalCohomology.kernelFunctor` — the objectwise kernel of a natural transformation of
  module-valued functors.

## Main results

* `Stacks.LocalCohomology.isIso_kernelFunctorMap_restriction` — degree-zero excision: sections
  vanishing on `V` are computed on `W`, by gluing.
* `Stacks.LocalCohomology.isZero_rightDerived_sectionsOnOpen_of_subsingleton` — derived sections
  over an open on which the sheaf vanishes are zero ([Stacks, Tag 01E1]).
* `Stacks.LocalCohomology.isIso_rightDerived_sectionsOnOpenRestriction_of_subsingleton` —
  **excision in every degree.**

## Implementation notes

The proof never chooses a resolution: the kernel of `Γ(Y, -) ⟶ Γ(V, -)` sits in a sequence of
functors that is short exact on injective objects (injective sheaves of modules are flasque,
`Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective`), and so does the
kernel of `Γ(W, -) ⟶ Γ(V ⊓ W, -)`; the two kernels are isomorphic functors, and the long exact
sequences of right derived functors (`CategoryTheory.isIso_rightDerived_app_of_isZero`,
`CategoryTheory.isZero_rightDerived_of_isZero`) do the rest.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleComparison

universe u

namespace Stacks.LocalCohomology

section RingedSpace

variable (X : RingedSpace.{u, u})

/-- **Restriction of sections between two opens**, linear over the global functions, naturally in
the sheaf of modules: the restriction maps of the presheaf of modules, with the scalars of the
target restricted along the composite `Γ(X, ⊤) → Γ(X, V) → Γ(X, V')`. -/
def sectionsOnOpenRestriction {V V' : Opens X} (h : V' ≤ V) :
    sectionsOnOpen X V ⟶ sectionsOnOpen X V' :=
  Functor.whiskerRight
      (Functor.whiskerLeft (SheafOfModules.forget (structureSheafRing X))
        (PresheafOfModules.restriction (structureSheafRing X).obj (homOfLE h).op))
      (ModuleCat.restrictScalars
        ((structureSheafRing X).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom) ≫
    Functor.whiskerLeft (SheafOfModules.evaluation (structureSheafRing X) (op V'))
      (ModuleCat.restrictScalarsComp'
        ((structureSheafRing X).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom
        ((structureSheafRing X).obj.map (homOfLE h).op).hom
        ((structureSheafRing X).obj.map (homOfLE (le_top : V' ≤ ⊤)).op).hom
        (by rw [← RingCat.hom_comp, ← Functor.map_comp]; rfl)).inv

/-- On elements, `sectionsOnOpenRestriction` is the restriction map of the sheaf. -/
theorem sectionsOnOpenRestriction_app_apply {V V' : Opens X} (h : V' ≤ V)
    (G : SheafOfModules.{u} (structureSheafRing X)) (x : (sectionsOnOpen X V).obj G) :
    (sectionsOnOpenRestriction X h).app G x = G.val.map (homOfLE h).op x :=
  rfl

/-- **Restriction is compatible with composition.** -/
theorem sectionsOnOpenRestriction_comp {V V' V'' : Opens X} (h : V' ≤ V) (h' : V'' ≤ V') :
    sectionsOnOpenRestriction X h ≫ sectionsOnOpenRestriction X h' =
      sectionsOnOpenRestriction X (h'.trans h) := by
  ext G x
  let y : G.val.obj (op V) := x
  exact (PresheafOfModules.map_comp_apply G.val (homOfLE h).op (homOfLE h').op y).symm

end RingedSpace

section Kernel

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {R : Type u} [Ring R] {F H : C ⥤ ModuleCat.{u} R}
  (q : F ⟶ H)

/-- The kernel of a natural transformation of module-valued functors, computed objectwise as the
kernel submodule. -/
def kernelFunctor : C ⥤ ModuleCat.{u} R where
  obj G := ModuleCat.of R (LinearMap.ker (q.app G).hom)
  map {G G'} f := ModuleCat.ofHom ((F.map f).hom.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    change (F.map f ≫ q.app G').hom x = 0
    rw [q.naturality, ModuleCat.comp_apply, show (q.app G).hom x = 0 from hx, map_zero])
  map_id G := by
    ext x
    change (F.map (𝟙 G)).hom x.1 = x.1
    rw [F.map_id]
    rfl
  map_comp f g := by
    ext x
    change (F.map (f ≫ g)).hom x.1 = (F.map g).hom ((F.map f).hom x.1)
    rw [F.map_comp]
    rfl

/-- The kernel functor of a natural transformation out of an additive functor is additive. -/
instance [Preadditive C] [F.Additive] : (kernelFunctor q).Additive where
  map_add {G G' f g} := by
    ext x
    refine Subtype.ext ?_
    change (F.map (f + g)).hom x.1 = (F.map f).hom x.1 + (F.map g).hom x.1
    rw [F.map_add]
    rfl

/-- The inclusion of the kernel functor. -/
def kernelFunctorι : kernelFunctor q ⟶ F where
  app G := ModuleCat.ofHom (LinearMap.ker (q.app G).hom).subtype
  naturality _ _ _ := rfl

/-- The inclusion of the kernel functor composed with `q` is zero. -/
theorem kernelFunctorι_comp : kernelFunctorι q ≫ q = 0 := by
  ext G x
  exact x.2

/-- The kernel functor sits in a short exact sequence at every object at which `q` is
surjective. -/
theorem shortExact_kernelFunctor (G : C) (hq : Function.Surjective (q.app G)) :
    (NatTrans.appShortComplex (kernelFunctorι q) q (kernelFunctorι_comp q) G).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro y
    exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).2 hq

/-- The map of kernel functors induced by a commutative square of natural transformations. -/
def kernelFunctorMap {F' H' : C ⥤ ModuleCat.{u} R} {q' : F' ⟶ H'} (α : F ⟶ F') (β : H ⟶ H')
    (comm : q ≫ β = α ≫ q') : kernelFunctor q ⟶ kernelFunctor q' where
  app G := ModuleCat.ofHom ((α.app G).hom.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    change (α.app G ≫ q'.app G).hom x = 0
    rw [← NatTrans.comp_app, ← comm, NatTrans.comp_app, ModuleCat.comp_apply,
      show (q.app G).hom x = 0 from hx, map_zero])
  naturality G G' f := by
    ext x
    refine Subtype.ext ?_
    change (F.map f ≫ α.app G').hom x.1 = (α.app G ≫ F'.map f).hom x.1
    rw [α.naturality]

/-- On elements, `kernelFunctorMap` is the restriction of `α` to the kernels. -/
theorem kernelFunctorMap_app_apply {F' H' : C ⥤ ModuleCat.{u} R} {q' : F' ⟶ H'} (α : F ⟶ F')
    (β : H ⟶ H') (comm : q ≫ β = α ≫ q') (G : C) (x : (kernelFunctor q).obj G) :
    ((kernelFunctorMap q α β comm).app G x).1 = α.app G x.1 :=
  rfl

end Kernel

section Gluing

variable (X : RingedSpace.{u, u})

/-- **Sections supported away from an open, computed on a neighbourhood of the support.** Let `V`
and `W` be opens covering `X`. Restriction to `W` identifies the global sections of a sheaf of
modules vanishing on `V` with the sections over `W` vanishing on `V ⊓ W`, naturally in the sheaf:
injectivity is the locality of the sheaf and surjectivity glues a section over `W` with the zero
section over `V`. -/
theorem isIso_kernelFunctorMap_restriction {V W : Opens X} (hVW : V ⊔ W = ⊤) :
    IsIso (kernelFunctorMap (sectionsOnOpenRestriction X (le_top : V ≤ ⊤))
      (sectionsOnOpenRestriction X (le_top : W ≤ ⊤))
      (sectionsOnOpenRestriction X (inf_le_left : V ⊓ W ≤ V))
      (q' := sectionsOnOpenRestriction X (inf_le_right : V ⊓ W ≤ W))
      (by rw [sectionsOnOpenRestriction_comp, sectionsOnOpenRestriction_comp])) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun G => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  let 𝒢 : TopCat.Sheaf Ab.{u} X := ⟨G.val.presheaf, G.isSheaf⟩
  let U : Bool → Opens X := fun b => cond b V W
  have hsup : (⊤ : Opens X) ≤ iSup U := by rw [iSup_bool_eq]; exact hVW.ge
  let iUT : ∀ b, U b ⟶ ⊤ := fun b => homOfLE le_top
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine Subtype.ext (𝒢.eq_of_locally_eq' U ⊤ iUT hsup x.1 y.1 fun b => ?_)
    rcases b with _ | _
    · exact congrArg Subtype.val hxy
    · exact (x.2.trans y.2.symm : _)
  · have h0 : G.val.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op y.1 = 0 := y.2
    have hy : ∀ {O : Opens X} (h₁ : O ≤ W) (h₂ : O ≤ V ⊓ W),
        G.val.presheaf.map (homOfLE h₁).op y.1 = 0 := by
      intro O h₁ h₂
      have e : (homOfLE h₁).op = (homOfLE (inf_le_right : V ⊓ W ≤ W)).op ≫ (homOfLE h₂).op :=
        rfl
      let z : G.val.presheaf.obj (op W) := y.1
      change G.val.presheaf.map (homOfLE h₁).op z = 0
      rw [e, Functor.map_comp, ConcreteCategory.comp_apply]
      change G.val.presheaf.map (homOfLE h₂).op (G.val.presheaf.map _ y.1) = 0
      rw [h0, map_zero]
    obtain ⟨g, hg, -⟩ := 𝒢.existsUnique_gluing' U ⊤ iUT hsup
      (fun b => Bool.rec y.1 0 b) (by
        intro i j
        rcases i with _ | _ <;> rcases j with _ | _
        · rfl
        · exact (hy inf_le_left (le_of_eq (inf_comm W V))).trans (map_zero _).symm
        · exact (map_zero _).trans (hy inf_le_right le_rfl).symm
        · rfl)
    exact ⟨⟨g, hg true⟩, Subtype.ext (hg false)⟩

end Gluing

section Scheme

variable (Y : Scheme.{u})

/-- **Derived sections over an open on which the sheaf vanishes.** If a sheaf of modules on a
scheme has only the zero section over every open contained in `W`, all its derived sections over
`W` vanish: they are the cohomology of its restriction to the open subscheme `W`
([Stacks, Tag 01E1]), and that restriction is the zero sheaf. -/
theorem isZero_rightDerived_sectionsOnOpen_of_subsingleton {W : Y.Opens} (G : Y.Modules)
    (hG : ∀ O : Y.Opens, O ≤ W → Subsingleton (G.val.obj (op O))) (n : ℕ) :
    IsZero (((sectionsOnOpen Y.toRingedSpace W).rightDerived n).obj G) := by
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso Y W n).app G)
  have hres : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj G) := by
    refine Stacks.LocalCohomologySequence.isZero_of_faithful
      (SheafOfModules.forget W.toScheme.ringCatSheaf) ?_
    rw [IsZero.iff_id_eq_zero]
    refine PresheafOfModules.hom_ext fun O => ?_
    have : Subsingleton ((((SheafOfModules.forget W.toScheme.ringCatSheaf).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj G)).obj O)) :=
      hG (W.ι ''ᵁ O.unop) (Scheme.Hom.image_le_opensRange _ _ |>.trans
        (by rw [Scheme.Opens.opensRange_ι]))
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _
  let : HasDerivedCategory W.toScheme.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} Γ(W.toScheme, ⊤)) := HasDerivedCategory.standard _
  let : ((Stacks.Cohomology.AffineBase.moduleGlobalSections W.toScheme).rightDerived n).Additive :=
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Stacks.Cohomology.AffineBase.moduleGlobalSections W.toScheme)).additive n
  exact (ModuleCat.restrictScalars _).map_isZero
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections W.toScheme).rightDerived n).map_isZero
      hres)

/-- **Excision for derived sections.** Let `V` and `W` be opens covering a scheme `Y`, and let `G`
be a sheaf of modules on `Y` with only the zero section over every open contained in `W`. Then
restriction `H^p(Y, G) ⟶ H^p(V, G)` is an isomorphism in every degree.

The kernel of `Γ(Y, -) ⟶ Γ(V, -)` is exact on injectives, since injective sheaves of modules are
flasque, and restricting to `W` identifies it with the kernel of `Γ(W, -) ⟶ Γ(V ⊓ W, -)`, whose
derived functors at `G` vanish because those of `Γ(W, -)` and `Γ(V ⊓ W, -)` do. -/
theorem isIso_rightDerived_sectionsOnOpenRestriction_of_subsingleton {V W : Y.Opens}
    (hVW : V ⊔ W = ⊤) (G : Y.Modules)
    (hG : ∀ O : Y.Opens, O ≤ W → Subsingleton (G.val.obj (op O))) (p : ℕ) :
    IsIso ((NatTrans.rightDerived
      (sectionsOnOpenRestriction Y.toRingedSpace (le_top : V ≤ ⊤)) p).app G) := by
  let q := sectionsOnOpenRestriction Y.toRingedSpace (le_top : V ≤ ⊤)
  let q' := sectionsOnOpenRestriction Y.toRingedSpace (inf_le_right : V ⊓ W ≤ W)
  have hinj : ∀ (r s : Y.Opens) (h : s ≤ r) (I : Y.Modules), Injective I →
      Function.Surjective ((sectionsOnOpenRestriction Y.toRingedSpace h).app I) :=
    fun _ _ h I hI =>
      @Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective _ _ _ I hI _ _ h
  refine isIso_rightDerived_app_of_isZero (kernelFunctorι q) q (kernelFunctorι_comp q)
    (fun I hI => shortExact_kernelFunctor q I (hinj _ _ _ I hI)) G (fun n => ?_) p
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
    (@asIso _ _ _ _ _ (isIso_kernelFunctorMap_restriction Y.toRingedSpace hVW)) n).app G)
  exact isZero_rightDerived_of_isZero (kernelFunctorι q') q' (kernelFunctorι_comp q')
    (fun I hI => shortExact_kernelFunctor q' I (hinj _ _ _ I hI)) G
    (isZero_rightDerived_sectionsOnOpen_of_subsingleton Y G hG)
    (isZero_rightDerived_sectionsOnOpen_of_subsingleton Y G
      fun O hO => hG O (hO.trans inf_le_right)) n

end Scheme

variable (A : Type u) [CommRing A] (a : Ideal A)

/-- **Restriction of sections between opens of `U = Spec A ∖ V(a)`**, as `A`-linear maps,
naturally in the sheaf. -/
def complementOpenRestriction {V V' : (complementZeroLocus A a : Scheme).Opens} (h : V' ≤ V) :
    complementOpenSections A a V ⟶ complementOpenSections A a V' :=
  Functor.whiskerRight
    (sectionsOnOpenRestriction (complementZeroLocus A a : Scheme).toRingedSpace h)
    (ModuleCat.restrictScalars (complementTopScalars a))

end Stacks.LocalCohomology

end
