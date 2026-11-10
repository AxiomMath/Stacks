module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules

/-!
# Copowers of abelian presheaves by a presheaf of sets preserve local bijectivity

Let `T` be a presheaf of sets on a site `(C, J)`. The copower `M ↦ T ⊗ M`, which sends an abelian
presheaf `M` to `V ↦ ⊕_{t ∈ T(V)} M(V)`, carries locally injective (resp. locally surjective)
morphisms to locally injective (resp. locally surjective) ones: an element of a finite direct sum
is controlled by finitely many coordinates, and finitely many covering sieves have a covering
intersection. In particular it preserves the morphisms inverted by sheafification.

## Main definitions

* `Stacks.Sites.Copower.finsuppPresheaf`: the presheaf `V ↦ (T(V) →₀ M(V))`, and
  `finsuppCopowerIso` identifying it with `M.copower T`.

## Main results

* `Stacks.Sites.Copower.W_copowerMap`: if `η` is inverted by sheafification, so is
  `copowerMap η (𝟙 T)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Sites.Copower

variable {C : Type v} [Category.{u} C] (T : Cᵒᵖ ⥤ Type u)

/-- The presheaf `V ↦ (T(V) →₀ M(V))`. -/
@[simps]
def finsuppPresheaf (M : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (T.obj V →₀ M.obj V)
  map f := AddCommGrpCat.ofHom ((Finsupp.mapDomain.addMonoidHom (T.map f)).comp
    (Finsupp.mapRange.addMonoidHom (M.map f).hom))
  map_id V := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp [Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- The action of `finsuppPresheaf T M` on a restriction map, on elements. -/
private theorem finsuppPresheaf_map_apply {M : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : T.obj V →₀ M.obj V) :
    (finsuppPresheaf T M).map f x =
      Finsupp.mapDomain (T.map f) (Finsupp.mapRange (M.map f) (map_zero _) x) := rfl

variable {T} in
/-- The morphism of finsupp presheaves induced by a morphism of abelian presheaves. -/
@[simps]
def finsuppMap {M M' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (η : M ⟶ M') :
    finsuppPresheaf T M ⟶ finsuppPresheaf T M' where
  app V := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom (η.app V).hom)
  naturality V W f := by
    apply AddCommGrpCat.hom_ext
    refine Finsupp.addHom_ext fun t m => ?_
    have := ConcreteCategory.congr_hom (η.naturality f) m
    simp only [ConcreteCategory.comp_apply] at this
    change Finsupp.mapRange (η.app W) (map_zero _) (Finsupp.mapDomain (T.map f)
        (Finsupp.mapRange (M.map f) (map_zero _) (Finsupp.single t m))) =
      Finsupp.mapDomain (T.map f) (Finsupp.mapRange (M'.map f) (map_zero _)
        (Finsupp.mapRange (η.app V) (map_zero _) (Finsupp.single t m)))
    simp only [Finsupp.mapRange_single, Finsupp.mapDomain_single, this]

/-- `M.copower T` is the finsupp presheaf. -/
def finsuppCopowerIso (M : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    M.copower T ≅ finsuppPresheaf T M :=
  NatIso.ofComponents (fun V => (AddCommGrpCat.finsuppCopowerIso (M.obj V) (T.obj V)).symm)
    (fun {V W} f => by
      apply Sigma.hom_ext
      intro s
      rw [Functor.copower_map, Sigma.ι_comp_map'_assoc]
      dsimp only [Iso.symm_hom, Functor.copower_obj, finsuppPresheaf]
      rw [AddCommGrpCat.ι_finsuppCopowerIso_inv, ← Category.assoc,
        AddCommGrpCat.ι_finsuppCopowerIso_inv]
      ext m : 2
      change Finsupp.single _ _ = Finsupp.mapDomain (T.map f)
        (Finsupp.mapRange (M.map f) (map_zero _) (Finsupp.single s m))
      simp only [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl)

/-- `finsuppCopowerIso` carries the summand indexed by `s` to the functions supported at `s`. -/
@[reassoc]
lemma ι_finsuppCopowerIso_hom_app (M : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Cᵒᵖ) (s : T.obj V) :
    Sigma.ι (fun _ : T.obj V => M.obj V) s ≫ (finsuppCopowerIso T M).hom.app V =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom s) :=
  AddCommGrpCat.ι_finsuppCopowerIso_inv _ _ s

/-- `finsuppCopowerIso` is natural in `M`: it intertwines `copowerMap η (𝟙 T)` with `finsuppMap η`.
-/
lemma finsuppCopowerIso_naturality {M M' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (η : M ⟶ M') :
    Functor.copowerMap η (𝟙 T) ≫ (finsuppCopowerIso T M').hom =
      (finsuppCopowerIso T M).hom ≫ finsuppMap η := by
  ext V : 2
  apply Sigma.hom_ext
  intro s
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.ι_copowerMap_app_assoc,
    ι_finsuppCopowerIso_hom_app, ι_finsuppCopowerIso_hom_app_assoc]
  ext m
  change Finsupp.single s _ = Finsupp.mapRange (η.app V) (map_zero _) (Finsupp.single s m)
  simp only [Finsupp.mapRange_single]
  rfl

variable (J : GrothendieckTopology C)

/-- A finite intersection of covering sieves is covering. -/
lemma finset_inf_mem {X : C} {ι : Type*} (s : Finset ι) (S : ι → Sieve X)
    (h : ∀ i ∈ s, S i ∈ J X) : s.inf S ∈ J X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [J.top_mem X]
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {T}

/-- If `η` is locally injective, then so is `finsuppMap η`. -/
lemma isLocallyInjective_finsuppMap {M M' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (η : M ⟶ M')
    [Presheaf.IsLocallyInjective J η] :
    Presheaf.IsLocallyInjective J (finsuppMap (T := T) η) where
  equalizerSieve_mem {V} x y hxy := by
    classical
    change T.obj V →₀ M.obj V at x y
    have hxy' : ∀ t, η.app V (x t) = η.app V (y t) := fun t => by
      exact congrArg (fun z : T.obj V →₀ M'.obj V => z t) hxy
    refine J.superset_covering ?_ (finset_inf_mem J (x.support ∪ y.support)
      (fun t => Presheaf.equalizerSieve (F := M) (x t) (y t))
      (fun t _ => Presheaf.equalizerSieve_mem J η _ _ (hxy' t)))
    intro W f hf
    change (finsuppPresheaf T M).map f.op x = (finsuppPresheaf T M).map f.op y
    rw [finsuppPresheaf_map_apply, finsuppPresheaf_map_apply]
    congr 1
    ext t
    simp only [Finsupp.mapRange_apply]
    by_cases ht : t ∈ x.support ∪ y.support
    · exact (Finset.inf_le (f := fun t => Presheaf.equalizerSieve (F := M) (x t) (y t)) ht) f hf
    · simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at ht
      rw [ht.1, ht.2]

/-- If `η` is locally surjective, then so is `finsuppMap η`. -/
lemma isLocallySurjective_finsuppMap {M M' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (η : M ⟶ M')
    [Presheaf.IsLocallySurjective J η] :
    Presheaf.IsLocallySurjective J (finsuppMap (T := T) η) where
  imageSieve_mem {V} z := by
    classical
    change T.obj (op V) →₀ M'.obj (op V) at z
    refine J.superset_covering ?_ (finset_inf_mem J z.support
      (fun t => Presheaf.imageSieve η (z t))
      (fun t _ => Presheaf.imageSieve_mem J η _))
    intro W f hf
    have hm : ∀ t ∈ z.support, ∃ m : M.obj (op W), η.app (op W) m = M'.map f.op (z t) :=
      fun t ht => (Finset.inf_le (f := fun t => Presheaf.imageSieve η (z t)) ht) f hf
    let m : T.obj (op V) → M.obj (op W) := fun t =>
      if h : t ∈ z.support then (hm t h).choose else 0
    refine ⟨z.support.sum fun t => Finsupp.single (T.map f.op t) (m t), ?_⟩
    change (Finsupp.mapRange.addMonoidHom (η.app (op W)).hom)
        (∑ t ∈ z.support, Finsupp.single (T.map f.op t) (m t)) = (finsuppPresheaf T M').map f.op z
    rw [finsuppPresheaf_map_apply]
    conv_rhs => rw [← Finsupp.sum_single z, Finsupp.sum]
    rw [map_sum, Finsupp.mapRange_finsetSum, Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      Finsupp.mapDomain_single]
    congr 1
    simp only [m, dite_eq_left ht]
    exact (hm t ht).choose_spec

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The copower by a presheaf of sets preserves the morphisms inverted by sheafification.** -/
theorem W_copowerMap {M M' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (η : M ⟶ M') (hη : J.W η) (T : Cᵒᵖ ⥤ Type u) :
    J.W (Functor.copowerMap η (𝟙 T)) := by
  obtain ⟨h₁, h₂⟩ := (J.W_iff_isLocallyBijective η).1 hη
  have hW : J.W (finsuppMap (T := T) η) :=
    (J.W_iff_isLocallyBijective _).2
      ⟨isLocallyInjective_finsuppMap J η, isLocallySurjective_finsuppMap J η⟩
  refine (J.W.arrow_mk_iso_iff (Arrow.isoMk (finsuppCopowerIso T M) (finsuppCopowerIso T M')
    (finsuppCopowerIso_naturality T η).symm)).2 hW

end Stacks.Sites.Copower
