module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiHomAmalgamation

/-!
# Refining a covering in the sheaf condition for the presheaf of morphisms

Two general facts about the sheaf condition for a presieve: separatedness passes from a
presieve to any presieve it refines, and the sheaf condition for a composite covering follows
from the sheaf condition for the outer covering and for the inner coverings over the members of
the outer one, together with separatedness elsewhere.  Then, for the presheaf of morphisms
`CategoryTheory.Pseudofunctor.presheafHom` of the pullback pseudofunctor of sheaves of modules,
the Zariski sheaf condition and the sheaf condition for a faithfully flat morphism of affine
schemes, over an arbitrary object of the schemes over `S`.

## Main results

* `CategoryTheory.Presieve.isSeparatedFor_of_factorsThru` and
  `CategoryTheory.Presieve.IsSeparatedFor.of_factorsThru`: separatedness passes from a presieve to
  any presieve it refines — the second is the monotonicity statement, the first its form with a
  separated refinement chosen arrow by arrow.
* `CategoryTheory.Presieve.isSheafFor_of_bindArrows`: **the bind criterion.**  A presieve
  containing all the composites of an outer family with inner presieves over its members is a
  sheaf presieve, granted the sheaf condition for the outer family and for each inner presieve,
  and separated refinements of the inner presieves and of the presieve itself.  Unlike
  `CategoryTheory.Presieve.isSheafFor_bind`, the sheaf condition for the inner presieves is used
  only over the members of the outer family.
* `AlgebraicGeometry.isSheafFor_presheafHom_zariski_over`: the Zariski sheaf condition for the
  presheaf of morphisms, for a Zariski covering family of an arbitrary object of the schemes over
  the base.
* `AlgebraicGeometry.isSheafFor_presheafHom_over_mk` and
  `AlgebraicGeometry.isSheafFor_presheafHom_ofArrows_over_mk`: the sheaf condition for the
  presheaf of morphisms on the object `Over.mk a` of the schemes over `S`, for a covering of the
  source of `a`, from the sheaf condition for the inverse images of the modules over the terminal
  object of the schemes over that source.
* `AlgebraicGeometry.isSheafFor_presheafHom_specMap_over`: the one-element affine case of the
  full-faithfulness half of Stacks 023T on the object `Over.mk a`, for `a : Spec R₀ ⟶ S`.

## Implementation notes

`AlgebraicGeometry.isSheafFor_presheafHom_over_mk` transports the sheaf condition along
`CategoryTheory.Over.map` for a single pair of modules.  Its hypothesis is stated with
`AlgebraicGeometry.Scheme.Modules.pullback` rather than with the pullback pseudofunctor's action
on morphisms: the two are definitionally equal, but the pseudofunctor spelling of a module on `S`
is not type-correct at `implicit` transparency, so a `rewrite` against a statement written that
way fails — the conversion is therefore done by `change` inside the proof, where it is a
definitional unfolding, and never appears in a statement.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe w v u

namespace CategoryTheory.Presieve

variable {C : Type*} [Category C] {P : Cᵒᵖ ⥤ Type w} {X : C}

/-- Restricting a section twice is restricting along the composite. -/
private lemma map_op_map_op {A A' A'' : C} (a : A ⟶ A') (b : A' ⟶ A'') (s : P.obj (op A'')) :
    P.map a.op (P.map b.op s) = P.map (a ≫ b).op s := by
  rw [op_comp, P.map_comp, types_comp_apply]

/-- If `i ≫ e = g ≫ f` and `e` restricts `t` to `y`, then restricting `t` along `f` and then `g`
is restricting `y` along `i`. -/
private lemma map_op_map_op_eq_of_comp {A B C' D : C} {f : A ⟶ B} {g : D ⟶ A} {i : D ⟶ C'}
    {e : C' ⟶ B} (hcomm : i ≫ e = g ≫ f) {t : P.obj (op B)} {y : P.obj (op C')}
    (ht : P.map e.op t = y) : P.map g.op (P.map f.op t) = P.map i.op y := by
  rw [map_op_map_op, ← hcomm, ← map_op_map_op, ht]

/-- **Separatedness passes to a refined presieve**, in the form in which the refinement is chosen
one arrow at a time: if `P` is separated for `R`, and every arrow of `R` admits a presieve on its
source for which `P` is separated and which factors through `T` along it, then `P` is separated
for `T`. -/
theorem isSeparatedFor_of_factorsThru {R T : Presieve X} (hR : R.IsSeparatedFor P)
    (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f →
      ∃ R' : Presieve Y, R'.IsSeparatedFor P ∧ R'.FactorsThruAlong T f) :
    T.IsSeparatedFor P := by
  intro x t₁ t₂ h₁ h₂
  refine hR.ext fun Y f hf ↦ ?_
  obtain ⟨R', hR', hfac⟩ := h hf
  refine hR'.ext fun Z g hg ↦ ?_
  obtain ⟨W, i, e, he, hcomm⟩ := hfac hg
  have key : ∀ t, x.IsAmalgamation t → P.map g.op (P.map f.op t) = P.map i.op (x e he) :=
    fun t ht ↦ map_op_map_op_eq_of_comp hcomm (ht e he)
  rw [key t₁ h₁, key t₂ h₂]

/-- **Separatedness is monotone under refinement**: if every arrow of `R` factors through an arrow
of `T` and `P` is separated for `R`, then `P` is separated for `T`. -/
theorem IsSeparatedFor.of_factorsThru {R T : Presieve X} (hR : R.IsSeparatedFor P)
    (H : R.FactorsThru T) : T.IsSeparatedFor P :=
  isSeparatedFor_of_factorsThru hR fun Y f hf ↦ ⟨⊤, isSeparatedFor_top P, fun Z g _ ↦ by
    obtain ⟨W, i, e, he, hie⟩ := H hf
    exact ⟨W, g ≫ i, e, he, by rw [Category.assoc, hie]⟩⟩

variable {I : Type*} {W : I → C}

/-- The presieve of composites of a family of morphisms `u j : W j ⟶ X` with presieves `B j` on
its members. -/
def bindArrows (u : ∀ j, W j ⟶ X) (B : ∀ j, Presieve (W j)) : Presieve X :=
  fun _ h ↦ ∃ (j : I) (g : _ ⟶ W j), B j g ∧ h = g ≫ u j

/-- The composite `g ≫ u j` of an arrow `g` of `B j` with `u j` belongs to `bindArrows u B`. -/
lemma bindArrows_comp {u : ∀ j, W j ⟶ X} {B : ∀ j, Presieve (W j)} (j : I) {Z : C}
    {g : Z ⟶ W j} (hg : B j g) : bindArrows u B (g ≫ u j) :=
  ⟨j, g, hg, rfl⟩

/-- **The bind criterion for the sheaf condition.**  Let `u j : W j ⟶ X` be a family of
morphisms, `B j` a presieve on `W j` for each `j`, and `R` a presieve on `X` containing every
composite of an arrow of some `B j` with `u j`.  Then `P` is a sheaf for `R` as soon as it is a
sheaf for the family `u`, a sheaf for each `B j`, and separated for a presieve refining `B j`
over every object mapping to `W j` and for a presieve refining the composites over the source of
every arrow of `R`. -/
theorem isSheafFor_of_bindArrows (u : ∀ j, W j ⟶ X) (B : ∀ j, Presieve (W j)) (R : Presieve X)
    (hU : IsSheafFor P (ofArrows W u)) (hB : ∀ j, IsSheafFor P (B j))
    (hmem : bindArrows u B ≤ R)
    (hBsep : ∀ (j : I) ⦃Q : C⦄ (c : Q ⟶ W j),
      ∃ R' : Presieve Q, R'.IsSeparatedFor P ∧ R'.FactorsThruAlong (B j) c)
    (hRsep : ∀ ⦃Q : C⦄ ⦃h : Q ⟶ X⦄, R h →
      ∃ R' : Presieve Q, R'.IsSeparatedFor P ∧ R'.FactorsThruAlong (bindArrows u B) h) :
    IsSheafFor P R := by
  have hmem' : ∀ (j : I) ⦃Z : C⦄ ⦃g : Z ⟶ W j⦄, B j g → R (g ≫ u j) :=
    fun j _ g hg ↦ hmem _ _ (bindArrows_comp j hg)
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · refine isSeparatedFor_of_factorsThru hU.isSeparatedFor ?_
    rintro Z f ⟨j⟩
    exact ⟨B j, (hB j).isSeparatedFor, fun Z' g hg ↦ ⟨_, 𝟙 _, _, hmem' j hg, by simp⟩⟩
  · intro x hx
    have hy : ∀ j : I, ∃ t, ∀ ⦃Z : C⦄ (g : Z ⟶ W j) (hg : B j g),
        P.map g.op t = x (g ≫ u j) (hmem' j hg) := by
      intro j
      refine ((hB j) (fun Z g hg ↦ x (g ≫ u j) (hmem' j hg)) ?_).exists
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
      exact hx g₁ g₂ (hmem' j h₁) (hmem' j h₂) (by rw [← Category.assoc, hcomm, Category.assoc])
    choose t ht using hy
    have hcompat : Arrows.Compatible P u t := by
      intro j₁ j₂ Q c₁ c₂ hc
      obtain ⟨R₁, hR₁, hfac₁⟩ := hBsep j₁ c₁
      refine hR₁.ext fun Q' d hd ↦ ?_
      obtain ⟨V, i, e, he, hcomm⟩ := hfac₁ hd
      obtain ⟨R₂, hR₂, hfac₂⟩ := hBsep j₂ (d ≫ c₂)
      refine hR₂.ext fun Q'' d' hd' ↦ ?_
      obtain ⟨V', i', e', he', hcomm'⟩ := hfac₂ hd'
      rw [map_op_map_op d c₁, map_op_map_op d c₂]
      rw [map_op_map_op_eq_of_comp (f := d ≫ c₁) (by rw [Category.assoc, hcomm]) (ht j₁ e he),
        map_op_map_op_eq_of_comp (f := d ≫ c₂) hcomm' (ht j₂ e' he')]
      exact hx (d' ≫ i) i' (hmem' j₁ he) (hmem' j₂ he')
        (by simp only [Category.assoc, reassoc_of% hcomm, reassoc_of% hcomm', hc])
    obtain ⟨s, hs⟩ := ((isSheafFor_arrows_iff (P := P) (π := u)).1 hU t hcompat).exists
    refine ⟨s, fun Q h hh ↦ ?_⟩
    obtain ⟨R', hR', hfac⟩ := hRsep hh
    refine hR'.ext fun Q' d hd ↦ ?_
    obtain ⟨V, i, e, ⟨j, g, hg, rfl⟩, hcomm⟩ := hfac hd
    rw [map_op_map_op_eq_of_comp (y := x (g ≫ u j) (hmem' j hg)) hcomm
      (by rw [← map_op_map_op, hs j, ht j g hg])]
    exact (hx d i hh (hmem' j hg) hcomm.symm).symm

end CategoryTheory.Presieve

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The sieve on an object `Y` of the schemes over `S` generated by a family of morphisms to
`Y.left`, viewed as a family of morphisms to `Y`, corresponds under
`CategoryTheory.Sieve.overEquiv` to the sieve on `Y.left` generated by the family.  This is
`AlgebraicGeometry.overEquiv_symm_ofArrows` over an arbitrary object. -/
lemma overEquiv_symm_ofArrows_over (Y : Over S) {I : Type*} {U : I → Scheme.{u}}
    (u : ∀ i, U i ⟶ Y.left) :
    (Sieve.overEquiv Y).symm (Sieve.generate (Presieve.ofArrows U u)) =
      Sieve.generate (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ Y.hom))
        (fun i ↦ (Over.homMk (u i) : Over.mk (u i ≫ Y.hom) ⟶ Y))) := by
  apply (Sieve.overEquiv Y).injective
  change (Sieve.overEquiv Y) ((Sieve.overEquiv Y).symm (Sieve.generate (Presieve.ofArrows U u))) =
    (Sieve.overEquiv Y) (Sieve.generate (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ Y.hom))
      (fun i ↦ (Over.homMk (u i) : Over.mk (u i ≫ Y.hom) ⟶ Y))))
  rw [OrderIso.apply_symm_apply, Sieve.overEquiv_ofArrows]
  rfl

/-- **The Zariski sheaf condition for the presheaf of morphisms over an arbitrary object.**  For
all sheaves of modules `M` and `N` on `S`, every object `Y` of the schemes over `S` and every
Zariski covering family of `Y.left`, the presheaf of morphisms satisfies the sheaf condition for
the family read as a family of morphisms to `Y`.  Quasi-coherence is not assumed. -/
theorem isSheafFor_presheafHom_zariski_over (M N : S.Modules) (Y : Over S) {I : Type*}
    {U : I → Scheme.{u}} (u : ∀ i, U i ⟶ Y.left)
    (hu : Presieve.ofArrows U u ∈ Scheme.zariskiPrecoverage.{u} Y.left) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ Y.hom))
        (fun i ↦ (Over.homMk (u i) : Over.mk (u i ≫ Y.hom) ⟶ Y))) := by
  rw [Presieve.isSheafFor_iff_generate, ← overEquiv_symm_ofArrows_over Y u]
  have hz := isSheaf_presheafHom_zariski (S := S) M N
  rw [isSheaf_iff_isSheaf_of_type] at hz
  exact hz _ (GrothendieckTopology.overEquiv_symm_mem_over _ _ _
    (Precoverage.generate_mem_toGrothendieck hu))

/-- **Transporting the sheaf condition for the presheaf of morphisms to an object of the schemes
over `S`.**  Let `a : T ⟶ S` and let `R` be a sieve on the scheme `T`.  If the presheaf of
morphisms of the inverse images of `M` and `N` on `T` satisfies the sheaf condition for `R`, read
on the terminal object of the schemes over `T`, then the presheaf of morphisms of `M` and `N`
satisfies it on the object `Over.mk a` of the schemes over `S`. -/
theorem isSheafFor_presheafHom_over_mk {T : Scheme.{u}} (a : T ⟶ S) (R : Sieve T)
    (M N : S.Modules)
    (h : Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom
        ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback a).obj N))
      ((Sieve.overEquiv (Over.mk (𝟙 T))).symm R).arrows) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv (Over.mk a)).symm R).arrows := by
  change Presieve.IsSheafFor
    (modulePullbackPseudofunctor.presheafHom
      ((modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M)
      ((modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj N))
    ((Sieve.overEquiv (Over.mk (𝟙 T))).symm R).arrows at h
  rw [← Presieve.isSheafFor_iff_of_iso
      (modulePullbackPseudofunctor.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, hd, fac⟩
    replace fac := (Over.forget _).congr_map fac
    simp only [Over.forget_obj, Over.map_obj_left, Over.mk_left, Over.forget_map, Over.comp_left,
      Over.isoMk_inv_left, Iso.refl_inv, Category.comp_id, Over.map_map_left] at fac
    change R.arrows b.left
    rw [fac]
    exact R.downward_closed hd d.left

/-- **The sheaf condition for the presheaf of morphisms over an object `Over.mk a`, from the
sheaf condition over the terminal object of the schemes over the source of `a`**, for a covering
family rather than for a sieve. -/
theorem isSheafFor_presheafHom_ofArrows_over_mk {T : Scheme.{u}} (a : T ⟶ S) (M N : S.Modules)
    {I : Type*} {U : I → Scheme.{u}} (u : ∀ i, U i ⟶ T)
    (h : Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom
        ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback a).obj N))
      (Presieve.ofArrows (fun i ↦ Over.mk (u i))
        (fun i ↦ (Over.homMk (u i) : Over.mk (u i) ⟶ Over.mk (𝟙 T))))) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ (Over.mk a).hom))
        (fun i ↦ (Over.homMk (u i) : Over.mk (u i ≫ (Over.mk a).hom) ⟶ Over.mk a))) := by
  rw [Presieve.isSheafFor_iff_generate, ← overEquiv_symm_ofArrows_over (Over.mk a) u]
  refine isSheafFor_presheafHom_over_mk a (Sieve.ofArrows U u) M N ?_
  rw [overEquiv_symm_ofArrows u]
  exact (Presieve.isSheafFor_iff_generate _).1 h

/-- **The one-element affine case of the full-faithfulness half of Stacks 023T, over an arbitrary
object of the schemes over `S`.**  For a faithfully flat morphism `φ : R₀ ⟶ B₀` of commutative
rings, a morphism `a : Spec R₀ ⟶ S` and quasi-coherent modules `M` and `N` on `S`, the presheaf
of morphisms of `M` and `N` satisfies the sheaf condition for the one-element family of
`Spec.map φ` over the object `Over.mk a` of the schemes over `S`. -/
theorem isSheafFor_presheafHom_specMap_over {R₀ B₀ : CommRingCat.{u}} (φ : R₀ ⟶ B₀)
    (hφ : φ.hom.FaithfullyFlat) (a : Spec R₀ ⟶ S) (M N : S.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N)
      (Presieve.ofArrows (fun _ : PUnit.{1} ↦ Over.mk (Spec.map φ ≫ (Over.mk a).hom))
        (fun _ ↦ (Over.homMk (Spec.map φ) :
          Over.mk (Spec.map φ ≫ (Over.mk a).hom) ⟶ Over.mk a))) := by
  have : ((Scheme.Modules.pullback a).obj M).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback a M inferInstance
  have : ((Scheme.Modules.pullback a).obj N).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback a N inferInstance
  refine isSheafFor_presheafHom_ofArrows_over_mk a M N (fun _ : PUnit.{1} ↦ Spec.map φ) ?_
  exact (Pseudofunctor.bijective_toDescentData_map_iff
    (F := modulePullbackPseudofunctor) (fun _ : PUnit.{1} ↦ Spec.map φ) _ _).mp
    (Stacks.Descent.bijective_toDescentData_map_specMap φ hφ _ _)

end AlgebraicGeometry

end
