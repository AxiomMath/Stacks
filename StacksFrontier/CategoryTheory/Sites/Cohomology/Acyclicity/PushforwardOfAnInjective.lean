module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.FieldExtensionBaseChange

/-!
# The direct image of an injective module is totally acyclic

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `I` be an injective
sheaf of `O_C`-modules. Then the sheaf of abelian groups underlying the direct image `f_*I` is
totally acyclic in the sense of Stacks 072Y: its cohomology over every sheaf of sets on `D`
vanishes in positive degrees. This is Stacks 072Z.

The proof is the one the source gives. Cohomology over a sheaf of sets is `Ext` out of the free
abelian sheaf it generates, and that sheaf is sectionwise torsion free, so it is enough that
`Ext^{n+1}(T, f_*I)` vanish for every sectionwise torsion-free `T`. Torsion-freeness is stable
under subobjects and every abelian sheaf is covered by a torsion-free one, so the dévissage of
`ModuleSheafCohomology.ext_eq_zero_of_resolving` reduces the claim to degree one, where it is an
extension problem: a map into `f_*I` out of the first term of a short exact sequence with
torsion-free third term has to extend over the second. The adjunction `f⁻¹ ⊣ f_*` of abelian
sheaves transports that problem to the source topos, where the inverse image — being exact —
has carried the sequence to another of the same kind, and
`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree` makes `Ext^1` out of its third term into
the abelian sheaf underlying `I` vanish, which splits it.

## Main results

* `Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`: **Stacks 072Z**, the
  direct image of an injective module is totally acyclic.

## Implementation notes

The source ringed topos has all three of its universes equal. The reason is
`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree`, the vanishing that supplies the extension
over the source topos: it is stated only for a small site with its sheaves valued in the same
universe, and the extension-of-scalars machinery it is proved from is private to that module.
The target ringed topos keeps its three universes independent, and so does the universe of the
`Ext`-groups witnessing total acyclicity.

The comparison of the two direct images — of sheaves of modules and of abelian sheaves — is
obtained from the identification of the underlying sheaves of *sets*
(`Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules` and
`Stacks.Topos.AbelianPushforward.abelianPushforward_forgetIso`, each of which is the identity)
by `abelianSheafNatIsoOfUnderlying`. A natural transformation between additive functors into
abelian sheaves is additive in each component as soon as the underlying maps of sheaves of sets
are natural, because additivity of a component is naturality at the two projections of a
biproduct compared with naturality at their sum. Forgetting the group operations is faithful but
not full, so there is no cheaper route from the set-level identification.

## References

* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Stacks.Topos.AbelianPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

universe x v u w v' u' w'

namespace Stacks.Cohomology

/-! ### Transport of `Ext`-vanishing and of torsion-freeness -/

/-- A map out of the first term of a short exact sequence extends over the second as soon as
`Ext^1` out of the third term vanishes: the obstruction to extending is the image of the map
under the connecting map of the contravariant long exact sequence. -/
private lemma exists_extension_of_ext_one_eq_zero {A : Type u} [Category.{v} A] [Abelian A]
    [HasExt.{x} A] {S : ShortComplex A} (hS : S.ShortExact) (N : A)
    (h : ∀ e : Ext.{x} S.X₃ N 1, e = 0) (m : S.X₁ ⟶ N) :
    ∃ g : S.X₂ ⟶ N, S.f ≫ g = m := by
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS N (Ext.mk₀ m)
    (show 1 + 0 = 1 from rfl) (h _)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective S.X₂ N).2 y
  exact ⟨g, (Ext.mk₀_bijective S.X₁ N).1 (by rwa [← Ext.mk₀_comp_mk₀])⟩

/-- The inverse image of abelian sheaves along a morphism of topoi is additive. -/
private lemma additive_abelianInverseImage {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    (Sites.abelianInverseImage f).Additive := by
  have : HasZeroObject (Sheaf K AddCommGrpCat.{w'}) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf J AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have : (Sites.abelianInverseImage f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.additive_of_preserves_binary_products _

/-- The inverse image of abelian sheaves along a morphism of topoi preserves sectionwise
torsion-freeness: multiplication by a nonzero integer is a monomorphism on a torsion-free
sheaf, and an exact additive functor keeps it one. -/
private lemma isTorsionFree_abelianInverseImage {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (F : Sheaf K AddCommGrpCat.{w'})
    (hF : ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) (U : Cᵒᵖ) :
    Module.IsTorsionFree ℤ (((Sites.abelianInverseImage f).obj F).obj.obj U) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n y hy
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have hmono : Mono (n • 𝟙 F) := by
    have hmono' : Mono (n • 𝟙 F).hom := by
      have (V : Dᵒᵖ) : Mono ((n • 𝟙 F).hom.app V) :=
        (AddCommGrpCat.mono_iff_injective _).2 (IsSMulRegular.of_ne_zero hn)
      exact NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf K AddCommGrpCat.{w'}).mono_of_mono_map hmono'
  have := additive_abelianInverseImage f
  let L := Sites.abelianInverseImage f
  have hm : Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map (L.map (n • 𝟙 F))).app U) :=
    inferInstance
  have hi := (AddCommGrpCat.mono_iff_injective _).mp hm
  rw [Functor.map_zsmul, L.map_id] at hi
  change Function.Injective (fun z : (L.obj F).obj.obj U => n • z) at hi
  apply hi
  simpa only [smul_zero] using hy

/-- The free abelian sheaf generated by a sheaf of sets is sectionwise torsion free: it is the
sheafification of the sectionwise free abelian group, which is flat. -/
private lemma isTorsionFree_freeAbelianSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}] (K : Sheaf J (Type w))
    (U : Cᵒᵖ) :
    Module.IsTorsionFree ℤ (((Presheaf.freeAbelianSheaf J).obj K.obj).obj.obj U) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J (K.obj ⋙ AddCommGrpCat.free) (fun V ↦ by
    show Module.IsTorsionFree ℤ (FreeAbelianGroup (K.obj.obj V))
    exact Module.Flat.isTorsionFree) U

/-! ### Lifting an isomorphism of underlying sheaves of sets to abelian sheaves -/

/-- A natural transformation between the underlying set-valued functors of two additive functors
into abelian groups is additive at each object: additivity at a section is naturality at the two
projections of the biproduct `X ⊞ X`, compared with naturality at their sum. -/
def naturalTransformationAddHom {B : Type u} [Category.{v} B] [Preadditive B]
    [HasBinaryBiproducts B] (F G : B ⥤ AddCommGrpCat.{w}) [F.Additive] [G.Additive]
    (φ : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) (X : B) :
    F.obj X →+ G.obj X where
  toFun := φ.app X
  map_zero' := by
    simpa using ConcreteCategory.congr_hom (C := Type w) (φ.naturality (0 : X ⟶ X)) 0
  map_add' a b := by
    let z : F.obj (X ⊞ X) := F.map biprod.inl a + F.map biprod.inr b
    have hf : F.map (biprod.fst : X ⊞ X ⟶ X) z = a := by
      simp [z, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hg : F.map (biprod.snd : X ⊞ X ⟶ X) z = b := by
      simp [z, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hfst := ConcreteCategory.congr_hom (C := Type w)
      (φ.naturality (biprod.fst : X ⊞ X ⟶ X)) z
    have hsnd := ConcreteCategory.congr_hom (C := Type w)
      (φ.naturality (biprod.snd : X ⊞ X ⟶ X)) z
    have hsum := ConcreteCategory.congr_hom (C := Type w)
      (φ.naturality ((biprod.fst : X ⊞ X ⟶ X) + biprod.snd)) z
    change φ.app X (F.map _ z) = G.map _ (φ.app (X ⊞ X) z) at hsum hfst hsnd
    simpa only [Functor.map_add, AddCommGrpCat.hom_add_apply, hf, hg, ← hfst, ← hsnd] using hsum

/-- A natural transformation between the underlying sheaves of sets of two additive functors
into abelian sheaves is a natural transformation of the functors themselves. -/
def abelianSheafNatTransOfUnderlying {B : Type u} [Category.{v} B] [Preadditive B]
    [HasBinaryBiproducts B] {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    (F G : B ⥤ Sheaf J AddCommGrpCat.{w}) [F.Additive] [G.Additive]
    (φ : F ⋙ sheafCompose J (forget AddCommGrpCat) ⟶
      G ⋙ sheafCompose J (forget AddCommGrpCat)) : F ⟶ G where
  app X := { hom := {
    app U := AddCommGrpCat.ofHom (naturalTransformationAddHom
      (F ⋙ sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj U)
      (G ⋙ sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj U)
      { app Y := (φ.app Y).hom.app U
        naturality Y Z g := congrArg (fun k ↦ k.hom.app U) (φ.naturality g) } X)
    naturality U V g := by
      ext z
      exact ConcreteCategory.congr_hom (C := Type w) ((φ.app X).hom.naturality g) z } }
  naturality X Y g := by
    ext U z
    exact ConcreteCategory.congr_hom (C := Type w)
      (congrArg (fun k ↦ k.hom.app U) (φ.naturality g)) z

/-- An isomorphism between the underlying sheaves of sets of two additive functors into abelian
sheaves is an isomorphism of the functors themselves. -/
def abelianSheafNatIsoOfUnderlying {B : Type u} [Category.{v} B] [Preadditive B]
    [HasBinaryBiproducts B] {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
    (F G : B ⥤ Sheaf J AddCommGrpCat.{w}) [F.Additive] [G.Additive]
    (φ : F ⋙ sheafCompose J (forget AddCommGrpCat) ≅
      G ⋙ sheafCompose J (forget AddCommGrpCat)) : F ≅ G where
  hom := abelianSheafNatTransOfUnderlying J F G φ.hom
  inv := abelianSheafNatTransOfUnderlying J G F φ.inv
  hom_inv_id := by
    ext X U z
    exact ConcreteCategory.congr_hom (C := Type w)
      (congrArg (fun k ↦ k.hom.app U) (φ.hom_inv_id_app X)) z
  inv_hom_id := by
    ext X U z
    exact ConcreteCategory.congr_hom (C := Type w)
      (congrArg (fun k ↦ k.hom.app U) (φ.inv_hom_id_app X)) z

/-! ### Stacks 072Z -/

section Acyclicity

variable {X : RingedTopos.{u, u, u}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The direct image of sheaves of modules along a morphism of ringed topoi, followed by
forgetting the module structure, is forgetting the module structure followed by the direct image
of abelian sheaves: both have the direct image of the underlying sheaf of sets underlying
them, on the nose. -/
@[sga "4 IV 13.2.3" "partial"]
private def pushforwardModulesAbelianIso :
    pushforwardModules f ⋙ SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        abelianPushforward X.J f.toToposHom := by
  have : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have := additive_abelianInverseImage f.toToposHom
  have : (abelianPushforward X.J f.toToposHom).Additive :=
    (abelianInverseImageAdjPushforward X.J f.toToposHom).right_adjoint_additive
  exact abelianSheafNatIsoOfUnderlying Y.J _ _ (Iso.refl _)

variable [HasSheafify Y.J AddCommGrpCat.{w'}] [HasExt.{x} (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{w'})]
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [Injective I]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- `Ext` out of a sectionwise torsion-free abelian sheaf into the direct image of the abelian
sheaf underlying an injective module vanishes in positive degree. -/
private lemma ext_eq_zero_of_abelianPushforward (T : Sheaf Y.J AddCommGrpCat.{w'})
    (hT : ∀ U, Module.IsTorsionFree ℤ (T.obj.obj U)) (n : ℕ)
    (a : Ext.{x} T ((abelianPushforward X.J f.toToposHom).obj
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj I))
      (n + 1)) : a = 0 := by
  let adj := abelianInverseImageAdjPushforward X.J f.toToposHom
  refine ModuleSheafCohomology.ext_eq_zero_of_resolving
    (fun G : Sheaf Y.J AddCommGrpCat.{w'} => ∀ U, Module.IsTorsionFree ℤ (G.obj.obj U))
    (fun m _ hH ↦ ModuleSheafCohomology.isTorsionFree_of_mono Y.J m hH)
    (ModuleSheafCohomology.exists_isTorsionFree_epi Y.J) _ ?_ n T hT a
  apply ModuleSheafCohomology.ext_one_eq_zero_of_extension
  intro S hS hP m
  obtain ⟨g, hg⟩ := exists_extension_of_ext_one_eq_zero
    (ShortComplex.ShortExact.map_of_exact hS (Sites.abelianInverseImage f.toToposHom)) _
    (fun e => ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree X.J _ I _
      (isTorsionFree_abelianInverseImage f.toToposHom S.X₃ hP) 0 e)
    ((adj.homEquiv _ _).symm m)
  have hg' : (Sites.abelianInverseImage f.toToposHom).map S.f ≫ g =
    (adj.homEquiv _ _).symm m := hg
  exact ⟨adj.homEquiv _ _ g, by
    rw [← adj.homEquiv_naturality_left, hg', Equiv.apply_symm_apply]⟩

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **Stacks 072Z.** The sheaf of abelian groups underlying the direct image of an injective
sheaf of modules along a morphism of ringed topoi is totally acyclic: its cohomology over every
sheaf of sets on the target vanishes in positive degrees. -/
@[stacks 072Z]
theorem isTotallyAcyclic_pushforwardModules_of_injective :
    IsTotallyAcyclic Y.J ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      ((pushforwardModules f).obj I)) := by
  intro K p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  refine subsingleton_ext_of_iso_right ((pushforwardModulesAbelianIso f).app I) (n + 1) ?_
  exact subsingleton_of_forall_eq 0
    (ext_eq_zero_of_abelianPushforward f I _ (isTorsionFree_freeAbelianSheaf Y.J K) n)

end Acyclicity

end Stacks.Cohomology
