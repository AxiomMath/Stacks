module

public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.Topology.Sets.Closeds
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization

/-!
# The point of the pro-étale site at a point of a weakly contractible affine scheme

Let `X` be an affine scheme which is weakly contractible as an object of the pro-étale site, and
let `x` be a point of `X`. The clopen subsets of `X` containing `x` form a cofiltered family of
objects `U ↪ X` of the small pro-étale site `X_proét`, and every pro-étale covering of such a
`U` is refined by a decomposition of `X` into finitely many clopen pieces, one of which is a
smaller clopen neighbourhood of `x`. So this family is a point of the site `X_proét`: its fibre
functor sends an object `Y` to the germs at `x` of morphisms `U ⟶ Y`, and the fibre of a sheaf
`F` is the colimit of `F(U)` over the clopen neighbourhoods `U` of `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.ProEt.ClopenNhds x`: the clopen neighbourhoods of a point `x`.
* `AlgebraicGeometry.Scheme.ProEt.ofClopen U`: a clopen subset `U` of `X` as an object of
  `X_proét`.
* `AlgebraicGeometry.Scheme.ProEt.clopenNhdsFunctor x`: the clopen neighbourhoods of `x` as a
  diagram in `X_proét`.
* `AlgebraicGeometry.Scheme.ProEt.clopenPoint hX x`: the point of `X_proét` at `x`, for `X`
  weakly contractible and affine.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.exists_clopenNhds_comp_mem_of_mem`: a covering sieve of an
  object `Y` of `X_proét` contains, after restriction to a smaller clopen neighbourhood, every
  morphism from a clopen neighbourhood of `x` to `Y`.

## Implementation notes

The point is built with `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`, in any
universe containing the objects of `X_proét`, so that its fibre functors take values in the
universe of the sheaves of modules on `X_proét` considered in the chapter.

The refinement step does not use that a clopen subset of `X` is again weakly contractible: a
covering of a clopen neighbourhood `U` of `x` is completed by the complement of `U` to a covering
of `X`, which is refined by a clopen decomposition of `X` itself.

## References

* [Stacks Project, Tag 0992](https://stacks.math.columbia.edu/tag/0992)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ProetaleWContractible

universe w u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- A clopen subset of `X`, as an open subset. -/
abbrev clopenOpens (U : Clopens X) : X.Opens := U.toOpens

/-- A clopen subset of `X`, viewed as an object of the small pro-étale site of `X`. -/
def ofClopen (U : Clopens X) : X.ProEt :=
  ProEt.mk (clopenOpens U).ι

/-- The underlying scheme of `ofClopen U` is the open subscheme `U`. -/
@[simp]
lemma ofClopen_left (U : Clopens X) : (ofClopen U).left = (clopenOpens U).toScheme := rfl

/-- The structure morphism of `ofClopen U` is the inclusion of `U` into `X`. -/
@[simp]
lemma ofClopen_hom (U : Clopens X) : (ofClopen U).hom = (clopenOpens U).ι := rfl

/-- A morphism to a clopen subset of `X` in `X_proét` is unique: the open immersion of the
clopen subset is a monomorphism over `X`. -/
instance (Y : X.ProEt) (U : Clopens X) : Subsingleton (Y ⟶ ofClopen U) := by
  refine ⟨fun f g => (ProEt.forgetFullyFaithful X).map_injective ?_⟩
  ext1
  have hf := Over.w ((ProEt.forget X).map f)
  have hg := Over.w ((ProEt.forget X).map g)
  exact (cancel_mono ((clopenOpens U).ι)).1 (hf.trans hg.symm)

/-- The inclusion of one clopen subset of `X` into a larger one, in `X_proét`. -/
def ofClopenHom {U V : Clopens X} (h : U ≤ V) : ofClopen U ⟶ ofClopen V :=
  MorphismProperty.Over.homMk (X.homOfLE (show (clopenOpens U) ≤ (clopenOpens V) from h))
    (Scheme.homOfLE_ι _ _)

/-- The clopen neighbourhoods of a point `x` of `X`, ordered by inclusion. -/
abbrev ClopenNhds (x : X) : Type u := {U : Clopens X // x ∈ U}

/-- Any two clopen neighbourhoods of `x` contain a third, their intersection. -/
instance (x : X) : IsCodirectedOrder (ClopenNhds x) :=
  ⟨fun U V => ⟨⟨U.1 ⊓ V.1, U.2, V.2⟩, inf_le_left (a := U.1), inf_le_right (a := U.1)⟩⟩

/-- The whole of `X` is a clopen neighbourhood of `x`. -/
instance (x : X) : Nonempty (ClopenNhds x) := ⟨⟨⊤, trivial⟩⟩

/-- The clopen neighbourhoods of `x` as a diagram in `X_proét`. -/
def clopenNhdsFunctor (x : X) : ClopenNhds x ⥤ X.ProEt where
  obj U := ofClopen U.1
  map f := ofClopenHom (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A morphism in `X_proét` to the final object `𝟙 X : X ⟶ X` is unique. -/
instance (Y : X.ProEt) : Subsingleton (Y ⟶ ProEt.mk (𝟙 X)) := by
  refine ⟨fun f g => (ProEt.forgetFullyFaithful X).map_injective ?_⟩
  ext1
  have hf := Over.w ((ProEt.forget X).map f)
  have hg := Over.w ((ProEt.forget X).map g)
  exact (cancel_mono (𝟙 X)).1 (hf.trans hg.symm)

/-- A clopen subset of `X` and its complement, as a clopen decomposition of `X`. -/
abbrev clopenPair (U : Clopens X) : Fin 2 → Clopens X := ![U, Uᶜ]

/-- A clopen subset `U` of `X` and its complement `Uᶜ` form a clopen decomposition of `X`. -/
lemma isClopenDecompositionCover_clopenPair (U : Clopens X) :
    IsClopenDecompositionCover (fun i => (clopenOpens (clopenPair U i)).toScheme)
      (fun i => (clopenOpens (clopenPair U i)).ι) where
  openImmersion _ := inferInstance
  clopen i := by
    rw [Scheme.Opens.range_ι]
    exact (clopenPair U i).isClopen
  disjoint i j hij := by
    simp only [Scheme.Opens.range_ι]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_compl_right (a := (U : Set X))
    · exact disjoint_compl_left (a := (U : Set X))
    · exact absurd rfl hij
  cover := by
    ext y
    simp only [Scheme.Opens.range_ι, Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hy : y ∈ U
    · exact ⟨0, hy⟩
    · exact ⟨1, hy⟩

/-- Every point of `T` lies in the image of some member of a clopen decomposition of `T`. -/
private lemma exists_mem_range_of_isClopenDecompositionCover {n : ℕ} {T : Scheme.{u}}
    {Z : Fin n → Scheme.{u}} {w : (i : Fin n) → Z i ⟶ T} (hw : IsClopenDecompositionCover Z w)
    (x : T) : ∃ i, x ∈ Set.range (w i).base :=
  Set.mem_iUnion.mp (by rw [hw.cover]; trivial)

/-- A morphism into a clopen subset `U` of `X`, composed with the inclusion, has range in `U`. -/
private lemma range_subset_of_comp_ι_eq {A : Scheme.{u}} {U : Clopens X}
    (k : A ⟶ (clopenOpens U).toScheme) {g : A ⟶ X} (hk : k ≫ (clopenOpens U).ι = g) :
    Set.range g ⊆ (U : Set X) := by
  subst hk
  rintro _ ⟨z, rfl⟩
  exact (Scheme.Opens.range_ι (clopenOpens U)).subset ⟨k z, (Scheme.Hom.comp_apply _ _ z).symm⟩

/-- If the image of an open immersion `w` is a clopen subset `V`, then the inclusion of `V`
factors through `w`. -/
private lemma exists_lift_clopenOpens_ι {Z : Scheme.{u}} (w : Z ⟶ X) [IsOpenImmersion w]
    (V : Clopens X) (hV : (V : Set X) = Set.range w.base) :
    ∃ l : (clopenOpens V).toScheme ⟶ Z, l ≫ w = (clopenOpens V).ι :=
  ⟨IsOpenImmersion.lift w (clopenOpens V).ι
    ((Scheme.Opens.range_ι (clopenOpens V)).subset.trans hV.subset),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- An object of `X_proét` mapping to a clopen subset `U` of `X` lies over `U`. -/
lemma range_hom_subset_of_hom {Z : X.ProEt} {U : Clopens X} (k : Z ⟶ ofClopen U) :
    Set.range Z.hom ⊆ (U : Set X) := by
  exact range_subset_of_comp_ι_eq ((ProEt.forget X).map k).left
    (Over.w ((ProEt.forget X).map k))

variable [IsAffine X]

/-- **Clopen neighbourhoods refine coverings.** Let `X` be an affine scheme which is weakly
contractible as an object of the pro-étale site, `x` a point of `X`, `U` a clopen neighbourhood
of `x` and `f : U ⟶ Y` a morphism of `X_proét`. Every covering sieve of `Y` contains, up to
restriction to a smaller clopen neighbourhood `V` of `x`, the morphism `f`. -/
theorem exists_clopenNhds_comp_mem_of_mem (hX : IsWeaklyContractibleObj X) (x : X)
    {Y : X.ProEt} (R : Sieve Y) (hR : R ∈ ProEt.topology X Y) (U : ClopenNhds x)
    (f : ofClopen U.1 ⟶ Y) :
    ∃ (Z : X.ProEt) (g : Z ⟶ Y) (_ : R g) (V : ClopenNhds x) (q : V ⟶ U)
      (a : ofClopen V.1 ⟶ Z), a ≫ g = ofClopenHom (leOfHom q) ≫ f := by
  classical
  let T : X.ProEt := ProEt.mk (𝟙 X)
  have : IsAffine T.left := inferInstanceAs (IsAffine X)
  have hW : IsWContractible.{u, u} Γ(T.left, ⊤) := isWContractible_of_isWeaklyContractible X hX
  let S : Sieve T :=
    { arrows := fun {Z} _ => (∃ k : Z ⟶ ofClopen U.1, R (k ≫ f)) ∨
        Nonempty (Z ⟶ ofClopen U.1ᶜ)
      downward_closed := by
        rintro Z W _ (⟨k, hk⟩ | ⟨k⟩) e
        · exact Or.inl ⟨e ≫ k, by simpa using R.downward_closed hk e⟩
        · exact Or.inr ⟨e ≫ k.some⟩ }
  have hf : ∀ i, WeaklyEtale ((clopenOpens (clopenPair U.1 i)).ι ≫ T.hom) := fun i => by
    show WeaklyEtale ((clopenOpens (clopenPair U.1 i)).ι ≫ 𝟙 X)
    infer_instance
  have hS : S ∈ ProEt.topology X T := by
    refine (ProEt.topology X).transitive
      (sieve_ofArrows_clopenDecomposition_mem_topology T _
        (isClopenDecompositionCover_clopenPair U.1) hf) S ?_
    rintro Z h ⟨W, e, _, ⟨i⟩, rfl⟩
    have hi : ∀ i, ∃ k : clopenDecompositionObj T _ hf i ⟶ ofClopen (clopenPair U.1 i),
        True := fun i => ⟨MorphismProperty.Over.homMk (𝟙 _)
          ((Category.id_comp _).trans (Category.comp_id _).symm), trivial⟩
    fin_cases i
    · obtain ⟨k, -⟩ := hi 0
      refine (ProEt.topology X).superset_covering ?_
        ((ProEt.topology X).pullback_stable (e ≫ k) ((ProEt.topology X).pullback_stable f hR))
      intro Z' e' he'
      exact Or.inl ⟨e' ≫ e ≫ k, by simpa using he'⟩
    · obtain ⟨k, -⟩ := hi 1
      refine (ProEt.topology X).superset_covering ?_ ((ProEt.topology X).top_mem _)
      intro Z' e' _
      exact Or.inr ⟨e' ≫ e ≫ k⟩
  obtain ⟨n, W, w, hdec, hw, hmem⟩ := exists_clopenDecomposition_of_isWContractible T hW S hS
  obtain ⟨i, hi⟩ := exists_mem_range_of_isClopenDecompositionCover hdec x
  have hrange : Set.range (w i) = Set.range (clopenDecompositionObj T w hw i).hom :=
    congrArg (fun g : W i ⟶ X => Set.range g) (Category.comp_id (w i)).symm
  rcases hmem i with ⟨k, hk⟩ | ⟨k⟩
  · let V : Clopens X := ⟨Set.range (w i).base, hdec.clopen i⟩
    have hVU : V ≤ U.1 := fun y hy => range_hom_subset_of_hom k (hrange ▸ hy)
    have : IsOpenImmersion (w i : W i ⟶ X) := hdec.openImmersion i
    obtain ⟨l, hl⟩ := exists_lift_clopenOpens_ι (w i : W i ⟶ X) V rfl
    let a : ofClopen V ⟶ clopenDecompositionObj T w hw i :=
      MorphismProperty.Over.homMk l ((congrArg (l ≫ ·) (Category.comp_id _)).trans hl)
    refine ⟨_, k ≫ f, hk, ⟨V, hi⟩, homOfLE hVU, a, ?_⟩
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (Subsingleton.elim _ _)
  · exact (range_hom_subset_of_hom k.some (hrange ▸ hi) U.2).elim

/-- The clopen neighbourhoods of `x` form an initially small category. -/
instance (x : X) : InitiallySmall.{max (u + 1) w} (ClopenNhds x) :=
  initiallySmall_of_essentiallySmall _

/-- **The point of `X_proét` at a point `x` of a weakly contractible affine scheme `X`.** Its
neighbourhoods are the clopen subsets of `X` containing `x`, so the fibre of a sheaf `F` is the
colimit of `F(U)` over the clopen neighbourhoods `U` of `x`. -/
def clopenPoint (hX : IsWeaklyContractibleObj X) (x : X) :
    (ProEt.topology X).Point.{max (u + 1) w} :=
  GrothendieckTopology.Point.ofIsCofiltered (clopenNhdsFunctor x)
    (fun _ R hR U f => exists_clopenNhds_comp_mem_of_mem hX x R hR U f)

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-! ### The point of `X_proét` at a point of a weakly contractible affine object -/

section Over

variable (W : X.ProEt)

/-- The composite of the inclusion of a clopen subset of the underlying scheme of an object `W`
of `X_proét` with the structure morphism of `W` is weakly étale. -/
theorem weaklyEtale_clopenOpens_ι_comp (U : Clopens W.left) :
    WeaklyEtale ((clopenOpens U).ι ≫ W.hom) :=
  have : WeaklyEtale W.hom := W.prop
  inferInstance

/-- A clopen subset `U` of the underlying scheme of an object `W` of `X_proét`, viewed as an
object of `X_proét` over `W`. -/
def ofClopenOver (U : Clopens W.left) : X.ProEt :=
  @ProEt.mk X _ ((clopenOpens U).ι ≫ W.hom) (weaklyEtale_clopenOpens_ι_comp W U)

/-- The underlying scheme of `ofClopenOver W U` is the open subscheme `U` of `W`. -/
@[simp]
lemma ofClopenOver_left (U : Clopens W.left) :
    (ofClopenOver W U).left = (clopenOpens U).toScheme := rfl

/-- The inclusion of a clopen subset of `W` into `W`, in `X_proét`. -/
def ofClopenOverι (U : Clopens W.left) : ofClopenOver W U ⟶ W :=
  MorphismProperty.Over.homMk (clopenOpens U).ι rfl

/-- The underlying morphism of `ofClopenOverι W U` is the inclusion of `U` into `W`. -/
@[simp]
lemma ofClopenOverι_left (U : Clopens W.left) :
    (ofClopenOverι W U).left = (clopenOpens U).ι := rfl

/-- Morphisms into a clopen subset of `W` are determined by their composites with the inclusion
into `W`: the inclusion of an open subscheme is a monomorphism. -/
theorem ofClopenOver_hom_ext {Y : X.ProEt} {U : Clopens W.left} {f g : Y ⟶ ofClopenOver W U}
    (h : f ≫ ofClopenOverι W U = g ≫ ofClopenOverι W U) : f = g := by
  refine (ProEt.forgetFullyFaithful X).map_injective ?_
  ext1
  have h' : f.left ≫ (clopenOpens U).ι = g.left ≫ (clopenOpens U).ι :=
    congrArg (fun k => k.left) h
  exact (cancel_mono (clopenOpens U).ι).1 h'

/-- The inclusion of one clopen subset of `W` into a larger one, in `X_proét`. -/
def ofClopenOverHom {U V : Clopens W.left} (h : U ≤ V) : ofClopenOver W U ⟶ ofClopenOver W V :=
  MorphismProperty.Over.homMk (W.left.homOfLE (U := clopenOpens U) (V := clopenOpens V)
    fun _ hx => h hx) (Scheme.homOfLE_ι_assoc _ _ _)

/-- The inclusion `U ⟶ V` of clopen subsets of `W`, composed with the inclusion of `V` into `W`,
is the inclusion of `U` into `W`. -/
@[reassoc (attr := simp)]
lemma ofClopenOverHom_ι {U V : Clopens W.left} (h : U ≤ V) :
    ofClopenOverHom W h ≫ ofClopenOverι W V = ofClopenOverι W U := by
  refine (ProEt.forgetFullyFaithful X).map_injective ?_
  ext1
  exact W.left.homOfLE_ι (U := clopenOpens U) (V := clopenOpens V) fun _ hx => h hx

/-- The clopen neighbourhoods of a point `w` of the underlying scheme of `W` as a diagram in
`X_proét`. -/
def clopenNhdsOverFunctor (w : W.left) : ClopenNhds w ⥤ X.ProEt where
  obj U := ofClopenOver W U.1
  map f := ofClopenOverHom W (leOfHom f)
  map_id _ := ofClopenOver_hom_ext W (by simp)
  map_comp _ _ := ofClopenOver_hom_ext W (by simp)

/-- An object of `X_proét` mapping to `W` through a clopen subset `U` of `W` lies over `U`. -/
lemma range_left_subset_of_hom {Z : X.ProEt} {U : Clopens W.left} (k : Z ⟶ ofClopenOver W U)
    {g : Z ⟶ W} (hk : k ≫ ofClopenOverι W U = g) : Set.range g.left ⊆ (U : Set W.left) := by
  exact range_subset_of_comp_ι_eq k.left (by rw [← hk]; rfl)

/-- **Clopen neighbourhoods refine coverings, over a weakly contractible affine object.** Let
`W` be an affine object of `X_proét` whose ring of global sections is w-contractible, `w` a point
of `W`, `U` a clopen neighbourhood of `w` in `W` and `f : U ⟶ Y` a morphism of `X_proét`. Every
covering sieve of `Y` contains, up to restriction to a smaller clopen neighbourhood `V` of `w`,
the morphism `f`. -/
theorem exists_clopenNhdsOver_comp_mem_of_mem [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) (w : W.left) {Y : X.ProEt} (R : Sieve Y)
    (hR : R ∈ ProEt.topology X Y) (U : ClopenNhds w) (f : ofClopenOver W U.1 ⟶ Y) :
    ∃ (Z : X.ProEt) (g : Z ⟶ Y) (_ : R g) (V : ClopenNhds w) (q : V ⟶ U)
      (a : ofClopenOver W V.1 ⟶ Z), a ≫ g = ofClopenOverHom W (leOfHom q) ≫ f := by
  classical
  let S : Sieve W :=
    { arrows := fun {Z} h => (∃ k : Z ⟶ ofClopenOver W U.1, k ≫ ofClopenOverι W U.1 = h ∧
          R (k ≫ f)) ∨ ∃ k : Z ⟶ ofClopenOver W U.1ᶜ, k ≫ ofClopenOverι W U.1ᶜ = h
      downward_closed := by
        rintro Z Z' h (⟨k, hk, hkR⟩ | ⟨k, hk⟩) e
        · exact Or.inl ⟨e ≫ k, by rw [Category.assoc, hk], by
            simpa using R.downward_closed hkR e⟩
        · exact Or.inr ⟨e ≫ k, by rw [Category.assoc, hk]⟩ }
  have hf : ∀ i, WeaklyEtale ((clopenOpens (clopenPair U.1 i)).ι ≫ W.hom) := fun i =>
    weaklyEtale_clopenOpens_ι_comp W _
  let k : ∀ i, clopenDecompositionObj W _ hf i ⟶ ofClopenOver W (clopenPair U.1 i) := fun i =>
    MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp _)
  have hk : ∀ i, k i ≫ ofClopenOverι W _ = clopenDecompositionHom W _ hf i := fun i => by
    refine (ProEt.forgetFullyFaithful X).map_injective ?_
    ext1
    exact Category.id_comp _
  have hS : S ∈ ProEt.topology X W := by
    refine (ProEt.topology X).transitive
      (sieve_ofArrows_clopenDecomposition_mem_topology W _
        (isClopenDecompositionCover_clopenPair U.1) hf) S ?_
    rintro Z h ⟨Z', e, _, ⟨i⟩, rfl⟩
    fin_cases i
    · refine (ProEt.topology X).superset_covering ?_
        ((ProEt.topology X).pullback_stable (e ≫ k 0) ((ProEt.topology X).pullback_stable f hR))
      intro Z'' e' he'
      refine Or.inl ⟨e' ≫ e ≫ k 0, ?_, by simpa using he'⟩
      simp only [Category.assoc]
      exact congrArg (e' ≫ e ≫ ·) (hk 0)
    · refine (ProEt.topology X).superset_covering ?_ ((ProEt.topology X).top_mem _)
      intro Z'' e' _
      refine Or.inr ⟨e' ≫ e ≫ k 1, ?_⟩
      simp only [Category.assoc]
      exact congrArg (e' ≫ e ≫ ·) (hk 1)
  obtain ⟨n, Ws, ws, hdec, hw, hmem⟩ := exists_clopenDecomposition_of_isWContractible W hW S hS
  obtain ⟨i, hi⟩ := exists_mem_range_of_isClopenDecompositionCover hdec w
  have hrange : Set.range (ws i) = Set.range (clopenDecompositionHom W ws hw i).left := rfl
  rcases hmem i with ⟨k, hk, hkR⟩ | ⟨k, hk⟩
  · let V : Clopens W.left := ⟨Set.range (ws i).base, hdec.clopen i⟩
    have hVU : V ≤ U.1 := fun y hy => range_left_subset_of_hom W k hk (hrange ▸ hy)
    have : IsOpenImmersion (ws i : Ws i ⟶ W.left) := hdec.openImmersion i
    obtain ⟨l, hl⟩ := exists_lift_clopenOpens_ι (ws i : Ws i ⟶ W.left) V rfl
    let a : ofClopenOver W V ⟶ clopenDecompositionObj W ws hw i :=
      MorphismProperty.Over.homMk l (by
        show l ≫ ws i ≫ W.hom = (clopenOpens V).ι ≫ W.hom
        rw [← Category.assoc, hl])
    have ha : a ≫ k = ofClopenOverHom W hVU := by
      refine ofClopenOver_hom_ext W ?_
      rw [Category.assoc, hk, ofClopenOverHom_ι]
      refine (ProEt.forgetFullyFaithful X).map_injective ?_
      ext1
      exact hl
    refine ⟨_, k ≫ f, hkR, ⟨V, hi⟩, homOfLE hVU, a, ?_⟩
    rw [← Category.assoc, ha]
  · exact (range_left_subset_of_hom W k hk (hrange ▸ hi) U.2).elim

/-- **The point of `X_proét` at a point of a weakly contractible affine object.** For an affine
object `W` of `X_proét` whose ring of global sections is w-contractible and a point `w` of `W`,
the clopen neighbourhoods of `w` in `W`, viewed as objects of `X_proét`, form a point of the site
`X_proét`; the fibre of a sheaf `F` is the colimit of `F(U)` over these neighbourhoods. -/
def clopenPointOver [IsAffine W.left] (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) (w : W.left) :
    (ProEt.topology X).Point.{max (u + 1) w} :=
  GrothendieckTopology.Point.ofIsCofiltered (clopenNhdsOverFunctor W w)
    (fun _ R hR U f => exists_clopenNhdsOver_comp_mem_of_mem W hW w R hR U f)

/-- The fibre of the point `clopenPointOver W hW w` at `W` is nonempty: it contains the germ at
`w` of the inclusion of `W` into itself. -/
theorem nonempty_clopenPointOver_fiber_obj [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) (w : W.left) :
    Nonempty ((clopenPointOver.{w} W hW w).fiber.obj W) :=
  ⟨GrothendieckTopology.Point.ofIsCofiltered.fiberMk (p := clopenNhdsOverFunctor W w)
    (U := ⟨⊤, trivial⟩) (ofClopenOverι W ⊤ : (clopenNhdsOverFunctor W w).obj ⟨⊤, trivial⟩ ⟶ W)⟩

end Over

end AlgebraicGeometry.Scheme.ProEt
