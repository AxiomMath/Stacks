module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections

/-!
# Pullbacks of meromorphic functions

For a morphism of locally ringed spaces, pullbacks of meromorphic functions are *defined* when
the pullback of every regular section on the target is regular on every compatible open subset
of the source. On schemes this can be tested on compatible pairs of affine opens.

## Main definitions

* `AlgebraicGeometry.structureSheafSectionOver`: a section of the structure sheaf on an open
  `U`, regarded as a global section of the structure sheaf of the restriction to `U`.
* `AlgebraicGeometry.IsRegularSectionOn`: regularity of a section of the structure sheaf on an
  open subset of a locally ringed space.
* `AlgebraicGeometry.pullbackSection`: the pullback of a section on `V` to an open `U`
  contained in the inverse image of `V`.
* `AlgebraicGeometry.PullbacksMeromorphicSections`: pullback along the morphism preserves
  regular sections of the structure sheaf.

## Main results

* `AlgebraicGeometry.structureSheafSectionOver_val`: each component is the usual restriction
  map on sections.
* `AlgebraicGeometry.pullbacksMeromorphicSections_of_affine`: an affine criterion — it suffices
  that the maps on rings of sections over compatible affine opens preserve nonzerodivisors.

## Implementation notes

A section on an open `U` is viewed as a global section of the structure sheaf of the locally
ringed space `X.restrict U.isOpenEmbedding`, and `AlgebraicGeometry.IsRegularSection` then
expresses its regularity. For a scheme, this is the underlying locally ringed space of the
restricted scheme, so the stalkwise and affine criteria for regular sections apply directly.
For opens `U` and `V` with `U ⊆ f ⁻¹(V)`, pullback first uses the structure map over `V` and
then restricts to `U`; thus `PullbacksMeromorphicSections` quantifies explicitly over all open
subsets and all regular sections. In the affine criterion the coordinate rings of the affine
opens are represented intrinsically by their rings of sections.

## References

* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Lemma 31.23.5](https://stacks.math.columbia.edu/tag/02OU)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A section of the structure sheaf on `U`, regarded as a global section of the unit module
of the locally ringed space restricted to `U`. -/
noncomputable abbrev structureSheafSectionOver
    (X : LocallyRingedSpace.{u}) (U : Opens X) (s : X.presheaf.obj (op U)) : (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf (X.restrict
        U.isOpenEmbedding).presheaf
        ((Presheaf.isSheaf_iff_isSheaf_comp _ (X.restrict U.isOpenEmbedding).presheaf
          (forget₂ CommRingCat RingCat)).mp (X.restrict U.isOpenEmbedding).IsSheaf))).sections :=
  PresheafOfModules.sectionsMk (fun W => X.presheaf.map
    (homOfLE (show U.isOpenEmbedding.functor.obj W.unop ≤ U from fun _ hx => by
      obtain ⟨x, _, rfl⟩ := hx
      exact x.property)).op s)
    (by
      intro V W i
      change X.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op
        (X.presheaf.map _ s) = _
      rw [← X.presheaf.map_comp_apply]
      congr 2)

/-- The component of the restricted section is the restriction to the corresponding open
of the original space. -/
@[simp]
theorem structureSheafSectionOver_val
    (X : LocallyRingedSpace.{u}) (U : Opens X) (s : X.presheaf.obj (op U))
    (W : Opens U) (h : U.isOpenEmbedding.functor.obj W ≤ U) :
    (structureSheafSectionOver X U s).val (op W) = X.presheaf.map (homOfLE h).op s := rfl

/-- A section of the structure sheaf is regular on `U` when multiplication by all of its
restrictions is a monomorphism on the locally ringed space restricted to `U`. -/
noncomputable abbrev IsRegularSectionOn
    (X : LocallyRingedSpace.{u}) (U : Opens X) (s : X.presheaf.obj (op U)) : Prop :=
  IsRegularSection (X.restrict U.isOpenEmbedding).presheaf
    ((Presheaf.isSheaf_iff_isSheaf_comp _ (X.restrict U.isOpenEmbedding).presheaf
      (forget₂ CommRingCat RingCat)).mp (X.restrict U.isOpenEmbedding).IsSheaf)
    (structureSheafSectionOver X U s)

/-- Pull a section on `V` back to an open `U` contained in the inverse image of `V`. -/
noncomputable abbrev pullbackSection {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f.base).obj V)
    (s : Y.presheaf.obj (op V)) : X.presheaf.obj (op U) :=
  X.presheaf.map (homOfLE h).op (f.c.app (op V) s)

/-- Pullbacks of meromorphic functions are defined for `f` when the pullback to every compatible
pair of opens sends regular sections of the target structure sheaf to regular sections of the
source structure sheaf. -/
@[stacks 02OT, ega "IV 20.1.11" "M_f = M_X condition"]
noncomputable abbrev PullbacksMeromorphicSections
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f.base).obj V) (s : Y.presheaf.obj (op V)),
    IsRegularSectionOn Y V s → IsRegularSectionOn X U (pullbackSection f U V h s)

section AffineCriterion

private lemma isSMulRegular_iff_of_ringIso
    {A B : CommRingCat} (e : A ≅ B) (a : A) (b : B) (hab : e.hom a = b) :
    IsSMulRegular A a ↔ IsSMulRegular B b := by
  let er : A ≃+* B := RingEquiv.ofRingHom (ConcreteCategory.hom e.hom)
    (ConcreteCategory.hom e.inv)
    (by ext x; simp) (by ext x; simp)
  have hab' : er a = b := by simpa [er] using hab
  exact Equiv.isSMulRegular_congr (e := er.toEquiv) (r := a) (s := b)
    fun z => (er.map_mul a z).trans (congrArg (· * er z) hab')

/-- The germ of `structureSheafSectionOver X U s` at a point of `U`, transported along the
isomorphism identifying the stalks of `X` and of its restriction to `U`, is the germ of `s`. -/
private lemma structureSheafSectionOver_germ_map
    (X : LocallyRingedSpace.{u}) (U : Opens X) (s : X.presheaf.obj (op U))
    (x : U) :
    (X.restrictStalkIso U.isOpenEmbedding x).hom
        ((X.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial
          ((structureSheafSectionOver X U s).val (.op ⊤))) =
      X.presheaf.germ U x.1 x.2 s := by
  let sec := structureSheafSectionOver X U s
  let W : Opens ((Opens.toTopCat X.toTopCat).obj U) := ⊤
  let x' : ↑((Opens.toTopCat X.toTopCat).obj U) := x
  have htop : U.isOpenEmbedding.functor.obj W = U := by
    change U.isOpenEmbedding.functor.obj
      (⊤ : Opens ((Opens.toTopCat X.toTopCat).obj U)) = U
    exact Opens.isOpenEmbedding_obj_top U
  have hW : U.isOpenEmbedding.functor.obj W ≤ U := le_of_eq htop
  have hxW : (U.inclusion' x') ∈ U.isOpenEmbedding.functor.obj W := by
    rw [htop]
    exact x.property
  have hval := structureSheafSectionOver_val X U s W hW
  have hmapId : homOfLE hW = eqToHom htop := Subsingleton.elim _ _
  have h' := congrArg (fun φ => φ (sec.val (.op W)))
    (PresheafedSpace.restrictStalkIso_hom_eq_germ
      X.toPresheafedSpace U.isOpenEmbedding W x' trivial)
  rw [hval, hmapId] at h'
  have hres := X.presheaf.germ_res_apply (eqToHom htop) (U.inclusion' x') hxW s
  change (X.restrictStalkIso U.isOpenEmbedding x).hom
      ((X.restrict U.isOpenEmbedding).presheaf.germ W x' trivial (sec.val (.op W))) =
    X.presheaf.germ U x.1 x.2 s
  rw [hval, hmapId]
  exact h'.trans hres

/-- **Regularity on an open set is a condition on germs.** A section of the structure sheaf is
regular on `U` exactly when its germ at every point of `U` is a nonzerodivisor. This is
`AlgebraicGeometry.isRegularSection_iff_stalk` for the restriction to `U`, whose stalks are
those of the ambient space. -/
theorem isRegularSectionOn_iff_forall_isSMulRegular_germ
    (X : LocallyRingedSpace.{u}) (U : Opens X) (s : X.presheaf.obj (op U)) :
    IsRegularSectionOn X U s ↔
      ∀ (z : X) (hz : z ∈ U),
        IsSMulRegular (X.presheaf.stalk z) (X.presheaf.germ U z hz s) := by
  have key := fun x : U => isSMulRegular_iff_of_ringIso (X.restrictStalkIso U.isOpenEmbedding x)
    _ _ (structureSheafSectionOver_germ_map X U s x)
  exact (isRegularSection_iff_stalk (X.restrict U.isOpenEmbedding)
    (structureSheafSectionOver X U s)).trans
    ⟨fun h z hz => (key ⟨z, hz⟩).mp (h ⟨z, hz⟩), fun h x => (key x).mpr (h x.1 x.2)⟩

end AffineCriterion

/-- If the maps on rings of sections over every compatible pair of affine opens preserve
nonzerodivisors, then pullbacks of meromorphic functions are defined. -/
theorem pullbacksMeromorphicSections_of_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hregular : ∀ (V : Opens Y) (U : Opens X), IsAffineOpen V → IsAffineOpen U →
      ∀ (h : U ≤ (Opens.map f.base).obj V) (s : Y.presheaf.obj (op V)),
        IsSMulRegular (Y.presheaf.obj (op V)) s →
          IsSMulRegular (X.presheaf.obj (op U))
            (pullbackSection f.toLRSHom U V h s)) :
    PullbacksMeromorphicSections f.toLRSHom := by
  intro U V h s hs
  have key : ∀ {y : Y} (hy : y ∈ V), ∃ (V₀ : Opens Y) (hV₀V : V₀ ≤ V), IsAffineOpen V₀ ∧
      y ∈ V₀ ∧ IsSMulRegular (Y.presheaf.obj (op V₀)) (Y.presheaf.map (homOfLE hV₀V).op s) := by
    intro y hy
    let y' : Scheme.Opens.toScheme V := ⟨y, hy⟩
    obtain ⟨W, hW, hyW, _⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (by simp : y' ∈ (⊤ : Opens _))
    have : IsAffine W.toScheme := hW
    let g : W.toScheme ⟶ Y := Scheme.Opens.ι W ≫ Scheme.Opens.ι V
    let V₀ : Opens Y := V.isOpenEmbedding.functor.obj W
    have hV₀eq : g.opensRange = V₀ := by
      dsimp only [g, V₀]
      rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
      rfl
    have hV₀V : V₀ ≤ V := by
      dsimp only [V₀]
      change Set.image (ConcreteCategory.hom V.inclusion') W.carrier ⊆ V.carrier
      rintro z ⟨w, hw, rfl⟩
      exact w.property
    refine ⟨V₀, hV₀V, by rw [← hV₀eq]; exact isAffineOpen_opensRange g, ⟨y', hyW, rfl⟩, ?_⟩
    rw [← structureSheafSectionOver_val Y.toLocallyRingedSpace V s W hV₀V]
    exact (isRegularSection_iff_forall_isSMulRegular
      (Y.toLocallyRingedSpace.restrict V.isOpenEmbedding).toSheafedSpace
      (structureSheafSectionOver Y.toLocallyRingedSpace V s)).mp hs W
  refine (isRegularSectionOn_iff_forall_isSMulRegular_germ X.toLocallyRingedSpace U _).2
    fun z hz => ?_
  obtain ⟨V₀, hV₀V, hV₀, hzV₀, ht⟩ := key (h hz)
  obtain ⟨T, hT, hzT, hTO⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ U ⊓ (Opens.map f.base).obj V₀ from ⟨hz, hzV₀⟩)
  have hTU : T ≤ U := fun z hz => (hTO hz).1
  have hTV₀ : T ≤ (Opens.map f.base).obj V₀ := fun z hz => (hTO hz).2
  have hnat := congrArg (fun k => k s) ((f.toLRSHom).c.naturality (homOfLE hV₀V).op)
  simp only [CategoryTheory.comp_apply] at hnat
  have hsection : pullbackSection f.toLRSHom T V₀ hTV₀ (Y.presheaf.map (homOfLE hV₀V).op s) =
      X.presheaf.map (homOfLE hTU).op (pullbackSection f.toLRSHom U V h s) := by
    dsimp [pullbackSection]
    rw [hnat]
    change X.presheaf.map (homOfLE hTV₀).op
        (((TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf).map
          (homOfLE hV₀V).op ((f.toLRSHom).c.app (op V) s)) =
      X.presheaf.map (homOfLE hTU).op
        (X.presheaf.map (homOfLE h).op ((f.toLRSHom).c.app (op V) s))
    dsimp [TopCat.Presheaf.pushforward]
    rw [← X.presheaf.map_comp_apply, ← X.presheaf.map_comp_apply]
    congr 1
  rw [← X.presheaf.germ_res_apply (homOfLE hTU) z hzT, ← hsection]
  exact isSMulRegular_germ_of_isAffineOpen X hT (hregular V₀ T hV₀ hT hTV₀ _ ht) ⟨z, hzT⟩

end AlgebraicGeometry
