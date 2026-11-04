module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Restriction

/-!
# Injective sheaves have surjective restriction maps

For a sheaf of modules on a ringed space, injectivity implies that sections over an open
subset extend to every larger open subset. The same assertion is provided directly for
injective sheaves of abelian groups.

## Main definitions

* `supportedSubmodule M U` is the subsheaf of `M` whose sections over `V` are those vanishing on a
  neighbourhood of every point of `V` outside `U`. It is the realisation, inside sheaves of
  modules, of the extension by zero `j_!(M|_U)`; membership in it is
  `mem_supportedSubmodule_iff`.
* `directImageRestriction M U` and `toDirectImageRestriction M U` are the direct image along
  the inclusion of `U` of the restriction of `M`, and the unit of that adjunction.

## Main results

* `injective_restriction_surjective`: the restriction map of an injective sheaf of modules
  along an inclusion of open subsets is surjective.
* `injective_abelian_restriction_surjective`: the corresponding assertion for an injective
  object of `TopCat.Sheaf AddCommGrpCat X`.

## Implementation notes

A ringed space is represented by its sheaf of rings `R` on a topological space. The restriction map
is the map of the underlying presheaf of abelian groups associated to the inclusion of opens. The
extension by zero of the restriction of a sheaf `I` is realized as the subsheaf of sections of `I`
locally zero outside the open subset. The space, the rings and the modules live in independent
universes.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Cohomology.InjectiveRestriction

variable {X : Type u} [TopologicalSpace X]
variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}

/-- Restricting twice in `(Opens X)ᵒᵖ` agrees with restricting along any single map with
the same source and target, because the hom-sets are subsingletons. -/
private lemma restrictₛₗ_comp_eq (M : PresheafOfModules.{w} R.obj)
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (h : V ⟶ Z) (s : M.obj V) :
    M.restrictₛₗ g (M.restrictₛₗ f s) = M.restrictₛₗ h s :=
  (M.map_comp_apply f g s).symm.trans (M.congr_map_apply (Subsingleton.elim _ _) s)

/-- A section restricting to zero along `f` restricts to zero along any map factoring
through the target of `f`. -/
private lemma restrictₛₗ_eq_zero_of_factors (M : PresheafOfModules.{w} R.obj)
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (h : V ⟶ Z)
    {s : M.obj V} (hs : M.restrictₛₗ f s = 0) :
    M.restrictₛₗ h s = 0 :=
  (restrictₛₗ_comp_eq M f g h s).symm.trans
    ((congrArg (fun x => M.restrictₛₗ g x) hs).trans (map_zero _))

/-- Restricting twice along inclusions of opens is restricting along the composite. -/
private lemma restrict_comp (M : PresheafOfModules.{w} R.obj)
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (s : M.obj (op C)) :
    M.restrictₛₗ (homOfLE hAB).op (M.restrictₛₗ (homOfLE hBC).op s) =
      M.restrictₛₗ (homOfLE (hAB.trans hBC)).op s :=
  restrictₛₗ_comp_eq M _ _ _ s

/-- Sections locally zero outside an open subset form a subsheaf of modules. -/
public def supportedSubmodule (M : SheafOfModules.{w} R) (U : Opens X) : M.Submodule where
  obj V :=
    { carrier := {s | ∀ x ∈ V.unop, x ∉ U → ∃ (W : Opens X) (hWV : W ≤ V.unop),
        x ∈ W ∧ M.val.restrictₛₗ (homOfLE hWV).op s = 0}
      zero_mem' := by
        intro x hx _
        exact ⟨V.unop, le_rfl, hx, map_zero _⟩
      add_mem' := by
        intro s t hs ht x hx hxU
        obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
        obtain ⟨Z, hZ, hxZ, htZ⟩ := ht x hx hxU
        refine ⟨W ⊓ Z, inf_le_left.trans hW, ⟨hxW, hxZ⟩, ?_⟩
        rw [map_add, ← restrict_comp M.val inf_le_left hW,
          ← restrict_comp M.val inf_le_right hZ, hsW, htZ, map_zero, map_zero, add_zero]
      smul_mem' := by
        intro r s hs x hx hxU
        obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
        refine ⟨W, hW, hxW, ?_⟩
        change M.val.restrictₛₗ (homOfLE hW).op (r • s) = 0
        rw [map_smulₛₗ, hsW, smul_zero] }
  map {V W} f := by
    intro s hs x hx hxU
    obtain ⟨Z, hZ, hxZ, hsZ⟩ := hs x (leOfHom f.unop hx) hxU
    refine ⟨Z ⊓ W.unop, inf_le_right, ⟨hxZ, hx⟩, ?_⟩
    change M.val.restrictₛₗ
      (homOfLE (show Z ⊓ W.unop ≤ W.unop from inf_le_right)).op
      (M.val.restrictₛₗ f s) = 0
    refine (restrictₛₗ_comp_eq M.val f _
      ((homOfLE hZ).op ≫
        (homOfLE (show Z ⊓ W.unop ≤ Z from inf_le_left)).op) s).trans ?_
    exact restrictₛₗ_eq_zero_of_factors M.val (homOfLE hZ).op
      (homOfLE (show Z ⊓ W.unop ≤ Z from inf_le_left)).op _ hsZ
  isSheaf {V} s hs := by
    intro x hx hxU
    obtain ⟨W, f, hf, hxW⟩ := hs x hx
    obtain ⟨Z, hZ, hxZ, hsZ⟩ := hf x hxW hxU
    refine ⟨Z, hZ.trans (leOfHom f), hxZ, ?_⟩
    change M.val.restrictₛₗ (homOfLE hZ).op (M.val.restrictₛₗ f.op s) = 0 at hsZ
    exact (restrictₛₗ_comp_eq M.val f.op (homOfLE hZ).op _ s).symm.trans hsZ

/-- Membership in the subsheaf of sections locally zero outside an open subset. -/
public lemma mem_supportedSubmodule_iff (M : SheafOfModules.{w} R) (U : Opens X)
    {V : Opens X} (s : M.val.obj (op V)) :
    s ∈ (supportedSubmodule M U).obj (op V) ↔
      ∀ x ∈ V, x ∉ U → ∃ (W : Opens X) (hWV : W ≤ V),
        x ∈ W ∧ M.val.restrictₛₗ (homOfLE hWV).op s = 0 :=
  Iff.rfl

/-- Every section over an open subset of `U` is locally zero outside `U`, vacuously. -/
private lemma mem_supportedSubmodule_of_le (M : SheafOfModules.{w} R)
    {U V : Opens X} (h : V ≤ U) (s : M.val.obj (op V)) :
    s ∈ (supportedSubmodule M U).obj (op V) :=
  (mem_supportedSubmodule_iff M U s).2 fun _ hx hxU => (hxU (h hx)).elim

/-- Two sections of a type-valued sheaf on opens that agree locally everywhere are equal. -/
private theorem eq_of_locally_eq {F : (Opens X)ᵒᵖ ⥤ Type w}
    (hF : Presieve.IsSheaf (Opens.grothendieckTopology X) F) {V : Opens X} (s t : F.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V),
      x ∈ W ∧ F.map (homOfLE hWV).op s = F.map (homOfLE hWV).op t) : s = t := by
  choose W hW hxW heq using fun x : V => h x.1 x.2
  apply (hF.isSheafFor (.ofArrows W fun x => homOfLE (hW x)) ?_).isSeparatedFor.ext
  · rintro _ _ ⟨x⟩
    exact heq x
  · intro x hx
    exact ⟨W ⟨x, hx⟩, homOfLE (hW _), Sieve.ofArrows_mk _ _ _, hxW _⟩

/-- A section of a sheaf of modules that vanishes locally everywhere is zero. -/
public lemma eq_zero_of_locally_zero (M : SheafOfModules.{w} R)
    {V : Opens X} (s : M.val.obj (op V))
    (hs : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V),
      x ∈ W ∧ M.val.restrictₛₗ (homOfLE hWV).op s = 0) : s = 0 :=
  eq_of_locally_eq (F := M.val.presheaf ⋙ forget AddCommGrpCat)
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)) s 0 fun x hx => by
    obtain ⟨W, hWV, hxW, h⟩ := hs x hx
    exact ⟨W, hWV, hxW, h.trans (map_zero (M.val.restrictₛₗ (homOfLE hWV).op)).symm⟩

/-- The direct image along the inclusion of an open subset of the restriction of `M`. -/
public noncomputable abbrev directImageRestriction (M : SheafOfModules.{w} R)
    (U : Opens X) : SheafOfModules R :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj (M.over U)

/-- The unit of the restriction/direct-image adjunction at `M`. -/
public noncomputable abbrev toDirectImageRestriction (M : SheafOfModules.{w} R)
    (U : Opens X) : M ⟶ directImageRestriction M U :=
  (SheafOfModules.overPushforwardOverAdj U).unit.app M

/-- The subsheaf of sections locally zero outside `U` includes monomorphically into the
direct image of the restriction to `U`. -/
public lemma supportedSubmodule_toDirectImageRestriction_mono
    (M : SheafOfModules.{w} R) (U : Opens X) :
    Mono ((supportedSubmodule M U).ι ≫ toDirectImageRestriction M U) := by
  apply (SheafOfModules.forget R).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  apply Subtype.ext
  apply eq_zero_of_locally_zero M s.val
  intro x hx
  by_cases hxU : x ∈ U
  · let f : U ⊓ V.unop ⟶ U ⨯ V.unop :=
      prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right)
    refine ⟨U ⊓ V.unop, inf_le_right, ⟨hxU, hx⟩, ?_⟩
    change M.val.restrictₛₗ (prod.snd : U ⨯ V.unop ⟶ V.unop).op s.val = 0 at hs
    exact restrictₛₗ_eq_zero_of_factors M.val
      (prod.snd : U ⨯ V.unop ⟶ V.unop).op f.op _ hs
  · exact (mem_supportedSubmodule_iff M U s.val).mp s.property x hx hxU

/-- An injective sheaf of modules has surjective restriction maps. -/
@[stacks 01EA]
public theorem injective_restriction_surjective
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (I : SheafOfModules.{w} R) [Injective I]
    {U' U : Opens X} (h : U' ≤ U) :
    Function.Surjective (I.val.presheaf.map (homOfLE h).op) := by
  intro y
  let N := supportedSubmodule I U'
  let j := N.ι ≫ toDirectImageRestriction I U'
  have : Mono j := supportedSubmodule_toDirectImageRestriction_mono I U'
  let k := Injective.factorThru N.ι j
  let t : (directImageRestriction I U').val.obj (op U) :=
    I.val.restrictₛₗ (prod.fst : U' ⨯ U ⟶ U').op y
  let y₀ : N.toSheafOfModules.val.obj (op U') :=
    ⟨y, mem_supportedSubmodule_of_le I le_rfl y⟩
  have ht : (directImageRestriction I U').val.map (homOfLE h).op t =
      j.val.app (op U') y₀ := by
    show I.val.restrictₛₗ (prod.map (𝟙 U') (homOfLE h)).op
      (I.val.restrictₛₗ (prod.fst : U' ⨯ U ⟶ U').op y) =
        I.val.restrictₛₗ (prod.snd : U' ⨯ U' ⟶ U').op y
    exact restrictₛₗ_comp_eq I.val (prod.fst : U' ⨯ U ⟶ U').op _ _ y
  have hy := congrArg (fun f => f.val.app (op U') y₀) (Injective.comp_factorThru N.ι j)
  change k.val.app (op U') (j.val.app (op U') y₀) = y at hy
  refine ⟨k.val.app (op U) t, ?_⟩
  show I.val.map (homOfLE h).op (k.val.app (op U) t) = y
  rw [← PresheafOfModules.naturality_apply k.val, ht]
  exact hy

namespace Abelian

variable {X : TopCat.{u}}

/-- Restricting twice in `(Opens X)ᵒᵖ` agrees with restricting along any single map with
the same source and target, because the hom-sets are subsingletons. -/
private lemma abMap_comp_eq (M : TopCat.Presheaf AddCommGrpCat.{v} X)
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (h : V ⟶ Z) (s : M.obj V) :
    M.map g (M.map f s) = M.map h s :=
  (Functor.map_comp_apply M f g s).symm.trans
    (congrArg (fun k => M.map k s) (Subsingleton.elim _ _))

/-- Restricting twice along inclusions of opens is restricting along the composite. -/
private lemma restrict_comp (M : TopCat.Sheaf AddCommGrpCat.{v} X)
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (s : M.obj.obj (op C)) :
    M.obj.map (homOfLE hAB).op (M.obj.map (homOfLE hBC).op s) =
      M.obj.map (homOfLE (hAB.trans hBC)).op s :=
  abMap_comp_eq M.obj _ _ _ s

/-- Sections over `V` locally zero outside `U` form a subgroup. -/
public def supportedSubgroup (M : TopCat.Sheaf AddCommGrpCat.{v} X)
    (U V : Opens X) : AddSubgroup (M.obj.obj (op V)) where
  carrier := {s | ∀ x ∈ V, x ∉ U → ∃ (W : Opens X) (hWV : W ≤ V),
    x ∈ W ∧ M.obj.map (homOfLE hWV).op s = 0}
  zero_mem' := by
    intro x hx _
    exact ⟨V, le_rfl, hx, map_zero _⟩
  add_mem' := by
    intro s t hs ht x hx hxU
    obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
    obtain ⟨Z, hZ, hxZ, htZ⟩ := ht x hx hxU
    refine ⟨W ⊓ Z, inf_le_left.trans hW, ⟨hxW, hxZ⟩, ?_⟩
    rw [map_add, ← restrict_comp M inf_le_left hW,
      ← restrict_comp M inf_le_right hZ, hsW, htZ, map_zero, map_zero, add_zero]
  neg_mem' := by
    intro s hs x hx hxU
    obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
    exact ⟨W, hW, hxW, by rw [map_neg, hsW, neg_zero]⟩

/-- Restriction carries sections locally zero outside `U` to sections locally zero
outside `U`. -/
public lemma supportedSubgroup_map (M : TopCat.Sheaf AddCommGrpCat.{v} X)
    (U : Opens X) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    {s : M.obj.obj V} (hs : s ∈ supportedSubgroup M U V.unop) :
    M.obj.map f s ∈ supportedSubgroup M U W.unop := by
  intro x hx hxU
  obtain ⟨Z, hZ, hxZ, hsZ⟩ := hs x (leOfHom f.unop hx) hxU
  refine ⟨Z ⊓ W.unop, inf_le_right, ⟨hxZ, hx⟩, ?_⟩
  rw [← Functor.map_comp_apply]
  have he : f ≫ (homOfLE (show Z ⊓ W.unop ≤ W.unop from inf_le_right)).op =
      (homOfLE hZ).op ≫ (homOfLE (show Z ⊓ W.unop ≤ Z from inf_le_left)).op :=
    Subsingleton.elim _ _
  rw [he, Functor.map_comp_apply, hsZ, map_zero]

/-- The subfunctor of sections locally zero outside `U`. -/
public def supportedSubfunctor (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    Subfunctor (M.obj ⋙ forget AddCommGrpCat) where
  obj V := {s | s ∈ supportedSubgroup M U V.unop}
  map f _ hs := supportedSubgroup_map M U f hs

/-- The presheaf of sections locally zero outside `U`. -/
public def supportedPresheaf (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    TopCat.Presheaf AddCommGrpCat.{v} X where
  obj V := AddCommGrpCat.of (supportedSubgroup M U V.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨M.obj.map f s.val, supportedSubgroup_map M U f s.property⟩
      map_zero' := by ext; exact map_zero _
      map_add' := by intros; ext; exact map_add _ _ _ }
  map_id V := by ext; simp
  map_comp f g := by ext; simp

/-- The sheaf of sections locally zero outside `U`. -/
public def supportedSheaf (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{v} X where
  obj := supportedPresheaf M U
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf _ (supportedSubfunctor M U).toFunctor
    rw [(supportedSubfunctor M U).isSheaf_iff
      ((isSheaf_iff_isSheaf_of_type _ _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ M.property))]
    intro V s hs x hx hxU
    obtain ⟨W, f, hf, hxW⟩ := hs x hx
    obtain ⟨Z, hZ, hxZ, hsZ⟩ := hf x hxW hxU
    refine ⟨Z, hZ.trans (leOfHom f), hxZ, ?_⟩
    change M.obj.map (homOfLE hZ).op (M.obj.map f.op s) = 0 at hsZ
    exact (abMap_comp_eq M.obj f.op (homOfLE hZ).op _ s).symm.trans hsZ

/-- The inclusion of the sheaf of sections locally zero outside `U` into `M`. -/
public def supportedSheafι (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    supportedSheaf M U ⟶ M :=
  ⟨{ app V := AddCommGrpCat.ofHom (supportedSubgroup M U V.unop).subtype }⟩

/-- A section of an abelian sheaf that vanishes locally everywhere is zero. -/
private lemma eq_zero_of_locally_zero (M : TopCat.Sheaf AddCommGrpCat.{v} X)
    {V : Opens X} (s : M.obj.obj (op V))
    (hs : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V),
      x ∈ W ∧ M.obj.map (homOfLE hWV).op s = 0) : s = 0 :=
  eq_of_locally_eq (F := M.obj ⋙ forget AddCommGrpCat)
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ M.property)) s 0 fun x hx => by
    obtain ⟨W, hWV, hxW, h⟩ := hs x hx
    exact ⟨W, hWV, hxW, h.trans (map_zero (M.obj.map (homOfLE hWV).op).hom).symm⟩

/-- The direct image along the inclusion of an open subset of the restriction of `M`. -/
public noncomputable abbrev directImageRestriction
    (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  ((Over.star U).sheafPushforwardContinuous AddCommGrpCat
    (Opens.grothendieckTopology X) ((Opens.grothendieckTopology X).over U)).obj (M.over U)

/-- The canonical map from `M` to the direct image of its restriction to `U`. -/
public noncomputable def toDirectImageRestriction
    (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    M ⟶ directImageRestriction M U :=
  ⟨{ app V := M.obj.map prod.snd.op
     naturality V W f := by
       ext s
       exact (abMap_comp_eq M.obj f (prod.snd : U ⨯ W.unop ⟶ W.unop).op
           (f ≫ (prod.snd : U ⨯ W.unop ⟶ W.unop).op) s).trans
         (abMap_comp_eq M.obj (prod.snd : U ⨯ V.unop ⟶ V.unop).op
           (((Over.star U).map f.unop).left).op
           (f ≫ (prod.snd : U ⨯ W.unop ⟶ W.unop).op) s).symm }⟩

/-- The sheaf of sections locally zero outside `U` includes monomorphically into the direct
image of the restriction to `U`. -/
private lemma supportedSheaf_toDirectImageRestriction_mono
    (M : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X) :
    Mono (supportedSheafι M U ≫ toDirectImageRestriction M U) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ ?_
  intro V
  apply ConcreteCategory.mono_of_injective
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  apply Subtype.ext
  apply eq_zero_of_locally_zero M s.val
  intro x hx
  by_cases hxU : x ∈ U
  · let f : U ⊓ V.unop ⟶ U ⨯ V.unop :=
      prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right)
    refine ⟨U ⊓ V.unop, inf_le_right, ⟨hxU, hx⟩, ?_⟩
    change M.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s.val = 0 at hs
    exact (abMap_comp_eq M.obj (prod.snd : U ⨯ V.unop ⟶ V.unop).op f.op _ s.val).symm.trans
      (by rw [hs, map_zero])
  · exact s.property x hx hxU

end Abelian

/-- An injective sheaf of abelian groups has surjective restriction maps. -/
public theorem injective_abelian_restriction_surjective
    {X : TopCat.{u}} (I : TopCat.Sheaf AddCommGrpCat.{v} X) [Injective I]
    {U' U : Opens X} (h : U' ≤ U) :
    Function.Surjective (I.presheaf.map (homOfLE h).op) := by
  intro y
  let j := Abelian.supportedSheafι I U' ≫ Abelian.toDirectImageRestriction I U'
  have : Mono j := Abelian.supportedSheaf_toDirectImageRestriction_mono I U'
  let k := Injective.factorThru (Abelian.supportedSheafι I U') j
  let t : (Abelian.directImageRestriction I U').obj.obj (op U) :=
    I.obj.map (prod.fst : U' ⨯ U ⟶ U').op y
  let y₀ : (Abelian.supportedSheaf I U').obj.obj (op U') :=
    ⟨y, fun _ hx hxU => (hxU hx).elim⟩
  have ht : (Abelian.directImageRestriction I U').obj.map (homOfLE h).op t =
      j.hom.app (op U') y₀ := by
    show I.obj.map (prod.map (𝟙 U') (homOfLE h)).op
      (I.obj.map (prod.fst : U' ⨯ U ⟶ U').op y) =
        I.obj.map (prod.snd : U' ⨯ U' ⟶ U').op y
    rw [← Functor.map_comp_apply]
    congr 2
  have hy := congrArg (fun f => f.hom.app (op U') y₀)
    (Injective.comp_factorThru (Abelian.supportedSheafι I U') j)
  change k.hom.app (op U') (j.hom.app (op U') y₀) = y at hy
  refine ⟨k.hom.app (op U) t, ?_⟩
  show I.obj.map (homOfLE h).op (k.hom.app (op U) t) = y
  rw [← ConcreteCategory.comp_apply, ← k.hom.naturality, ConcreteCategory.comp_apply, ht]
  exact hy

end Stacks.Cohomology.InjectiveRestriction

end
