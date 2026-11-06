module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.DisjointCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftClassSingleCover

/-!
# The sheaf condition of Stacks 0DNS for a standard fppf covering

Let `F` be the functor of isomorphism classes of lifts of Stacks 0DNS. For a finite family
`{Y_k ⟶ W}` of `Over U'` whose underlying morphisms of affine schemes form a standard fppf
covering, `F` satisfies the sheaf condition: write `V = ∐ Y_k`, so that `V ⟶ W` is one flat,
surjective, finitely presented morphism of affine schemes. Lift classes over `V` are families of
lift classes over the `Y_k`
(`Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.existsUnique_of_isDisjointCover`),
and the sheaf condition along `V ⟶ W` is
`Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.injective_map_of_fppf` and
`Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.exists_map_eq_of_fppf`; the double overlap
`V ×_W V` is covered disjointly by the `Y_k ×_W Y_l`.

## Main definitions and results

* `Deformation.Artin.LiftClassSheaf.pbObj`: fibre products in `Over U'`, through those of the big
  affine fppf site.
* `Deformation.Artin.LiftClassSheaf.coprodOver`: the coproduct `∐ Y_k` of a finite family of
  `Over U'`, through the coproduct of the big fppf site.
* `Deformation.Artin.LiftClassSheaf.LiftClassPresheaf.isSheafFor_ofArrows`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Deformation.Artin.LiftClassSheaf

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U' : BigAffineFppf B S hS}

/-! ### Fibre products in `Over U'` -/

/-- The fibre product `Z ×_V Y` in `Over U'`. -/
def pbObj {Z V Y : Over U'} (f : Z ⟶ V) (e : Y ⟶ V) : Over U' :=
  Over.mk (pullback.fst f.left e.left ≫ Z.hom)

/-- The first projection of `Z ×_V Y`. -/
def pbFst {Z V Y : Over U'} (f : Z ⟶ V) (e : Y ⟶ V) : pbObj f e ⟶ Z :=
  Over.homMk (pullback.fst f.left e.left)

/-- The second projection of `Z ×_V Y`. -/
def pbSnd {Z V Y : Over U'} (f : Z ⟶ V) (e : Y ⟶ V) : pbObj f e ⟶ Y :=
  Over.homMk (pullback.snd f.left e.left) (by
    simp only [pbObj, Over.mk_hom]
    rw [← Over.w e, ← Over.w f, pullback.condition_assoc])

/-- The square of the fibre product `Z ×_V Y` in `Over U'` commutes. -/
theorem pb_comm {Z V Y : Over U'} (f : Z ⟶ V) (e : Y ⟶ V) :
    pbFst f e ≫ f = pbSnd f e ≫ e :=
  Over.OverMorphism.ext pullback.condition

/-- The square of the fibre product `Z ×_V Y` is cartesian in the big fppf site. -/
theorem isPullback_pb {Z V Y : Over U'} (f : Z ⟶ V) (e : Y ⟶ V) :
    IsPullback ((BigAffineFppf.inclusion B S hS).map (pbFst f e).left)
      ((BigAffineFppf.inclusion B S hS).map (pbSnd f e).left)
      ((BigAffineFppf.inclusion B S hS).map f.left) ((BigAffineFppf.inclusion B S hS).map e.left) :=
  isPullback_inclusion_of_toScheme
    (IsPullback.map (BigAffineFppf.toScheme B S hS) (IsPullback.of_hasPullback f.left e.left))

/-! ### Finite coproducts in `Over U'` -/

section Sigma

variable {n : ℕ} (Y : Fin n → Over U')

/-- The underlying objects, in the big fppf site, of a finite family of `Over U'`. -/
abbrev sigmaFam : Fin n → BigFppfOver B S hS :=
  fun k ↦ (BigAffineFppf.inclusion B S hS).obj (Y k).left

/-- The comparison of the coproduct of schemes with the scheme of the coproduct. -/
abbrev sigmaCmp := sigmaComparison (BigFppfOver.toScheme B S hS) (sigmaFam Y)

/-- The scheme map of a coproduct injection of the big fppf site is the coproduct injection
of schemes followed by the comparison map. -/
theorem toScheme_map_sigma_ι (k : Fin n) :
    (BigFppfOver.toScheme B S hS).map (Sigma.ι (sigmaFam Y) k) =
      Sigma.ι (fun k ↦ (BigFppfOver.toScheme B S hS).obj (sigmaFam Y k)) k ≫ sigmaCmp Y :=
  (ι_comp_sigmaComparison _ _ _).symm

/-- The scheme map of the morphism out of a coproduct of the big fppf site induced by a
family is the inverse of the comparison map followed by the morphism induced on schemes. -/
theorem toScheme_map_sigma_desc {T : BigFppfOver B S hS} (gb : ∀ k, sigmaFam Y k ⟶ T) :
    (BigFppfOver.toScheme B S hS).map (Sigma.desc gb) =
      CategoryTheory.inv (sigmaCmp Y) ≫
        Sigma.desc fun k ↦ (BigFppfOver.toScheme B S hS).map (gb k) :=
  (IsIso.eq_inv_comp (sigmaCmp Y)).2 (sigmaComparison_map_desc _ _ _ _)

/-- The coproduct of a finite family of `Over U'` is affine. -/
theorem isAffine_sigmaBase : IsAffine ((BigFppfOver.toScheme B S hS).obj (∐ sigmaFam Y)) := by
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (sigmaFam Y k)) :=
    fun k ↦ (Y k).left.property
  exact IsAffine.of_isIso (CategoryTheory.inv (sigmaCmp Y))

/-- The coproduct `∐ Y_k` of a finite family of `Over U'`. -/
abbrev coprodOver : Over U' :=
  Over.mk (ObjectProperty.homMk
      (Sigma.desc fun k ↦ (BigAffineFppf.inclusion B S hS).map (Y k).hom) :
    (⟨∐ sigmaFam Y, isAffine_sigmaBase Y⟩ : BigAffineFppf B S hS) ⟶ U')

/-- The coproduct injections of `∐ Y_k`. -/
def sigmaι (k : Fin n) : Y k ⟶ coprodOver Y :=
  Over.homMk (ObjectProperty.homMk (Sigma.ι (sigmaFam Y) k))
    ((BigAffineFppf.inclusion B S hS).map_injective (by simp [coprodOver]))

/-- The morphism `∐ Y_k ⟶ W` induced by a family `Y_k ⟶ W`. -/
def sigmaDesc {W : Over U'} (g : ∀ k, Y k ⟶ W) : coprodOver Y ⟶ W :=
  Over.homMk
    (ObjectProperty.homMk (Sigma.desc fun k ↦ (BigAffineFppf.inclusion B S hS).map (g k).left))
    ((BigAffineFppf.inclusion B S hS).map_injective (by
      rw [Functor.map_comp]
      refine Sigma.hom_ext (f := sigmaFam Y) _ _ fun k ↦ ?_
      change Sigma.ι (sigmaFam Y) k ≫ Sigma.desc (fun k ↦ (BigAffineFppf.inclusion B S hS).map
          (g k).left) ≫ (BigAffineFppf.inclusion B S hS).map W.hom =
        Sigma.ι (sigmaFam Y) k ≫ Sigma.desc fun k ↦ (BigAffineFppf.inclusion B S hS).map (Y k).hom
      rw [Sigma.ι_desc_assoc, Sigma.ι_desc, ← Functor.map_comp, Over.w (g k)]))

/-- The morphism `∐ Y_k ⟶ W` induced by a family restricts to each member of the family. -/
@[reassoc (attr := simp)]
theorem sigmaι_sigmaDesc {W : Over U'} (g : ∀ k, Y k ⟶ W) (k : Fin n) :
    sigmaι Y k ≫ sigmaDesc Y g = g k :=
  Over.OverMorphism.ext ((BigAffineFppf.inclusion B S hS).map_injective (by
    simp [sigmaι, sigmaDesc]))

/-- **The coproduct injections form a disjoint covering family of the big fppf site.** -/
theorem isDisjointCover_sigmaι :
    IsDisjointCover (BigFppfOver.topology B S hS)
      (fun j : ULift.{w} (Fin n) ↦ (BigAffineFppf.inclusion B S hS).obj (Y j.down).left)
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (sigmaι Y j.down).left) := by
  refine BigFppfOver.isDisjointCover_of_isOpenImmersion _ _ (fun j ↦ ?_) (fun x ↦ ?_)
    (fun j j' hjj' Z a b hab ↦ ?_)
  · show IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (Sigma.ι (sigmaFam Y) j.down))
    rw [toScheme_map_sigma_ι]
    infer_instance
  · change ↥((BigFppfOver.toScheme B S hS).obj (∐ sigmaFam Y)) at x
    obtain ⟨k, z, hz⟩ :=
      (sigmaOpenCover (fun k ↦ (BigFppfOver.toScheme B S hS).obj (sigmaFam Y k))).exists_eq
        (CategoryTheory.inv (sigmaCmp Y) x)
    change Fin n at k
    change ↥((BigFppfOver.toScheme B S hS).obj (sigmaFam Y k)) at z
    change (Sigma.ι (fun k ↦ (BigFppfOver.toScheme B S hS).obj (sigmaFam Y k)) k) z = _ at hz
    refine ⟨⟨k⟩, z, ?_⟩
    show (BigFppfOver.toScheme B S hS).map (Sigma.ι (sigmaFam Y) k) z = x
    rw [toScheme_map_sigma_ι, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply,
      IsIso.inv_hom_id]
    rfl
  · refine isEmpty_of_commSq_sigmaι_of_ne
      (g := fun k ↦ (BigFppfOver.toScheme B S hS).obj (sigmaFam Y k))
      (a := (BigFppfOver.toScheme B S hS).map a) (b := (BigFppfOver.toScheme B S hS).map b) ⟨?_⟩
      (fun h ↦ hjj' (ULift.ext h))
    rw [← cancel_mono (sigmaCmp Y), Category.assoc, Category.assoc, ← toScheme_map_sigma_ι,
      ← toScheme_map_sigma_ι, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ hab

end Sigma

namespace LiftClassPresheaf

variable {U : BigAffineFppf B S hS} {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} {i : U ⟶ U'}
  {x : 𝒳.val.val.obj} {hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U}
  (P : LiftClassPresheaf B S hS 𝒳 i x hx)

/-- **The sheaf condition of Stacks 0DNS for a standard fppf covering.** -/
theorem isSheafFor_ofArrows
    (harr : Stack.GroupoidLift.ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳.val)
    (hi : IsDeformationSituation (ringMap B S hS i).hom) {W : Over U'} {n : ℕ}
    (Y : Fin n → Over U') (g : ∀ k, Y k ⟶ W)
    (hg : IsStandardFppfCovering (fun k ↦ (BigAffineFppf.toScheme B S hS).obj (Y k).left)
      (fun k ↦ (BigAffineFppf.toScheme B S hS).map (g k).left)) :
    Presieve.IsSheafFor P.presheaf (Presieve.ofArrows Y g) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  -- the single covering `∐ Y_k ⟶ W`
  obtain ⟨ko, hιk, hkf, hks, hkp⟩ : ∃ ko : coprodOver Y ⟶ W, (∀ k, sigmaι Y k ≫ ko = g k) ∧
      Flat ((BigAffineFppf.toScheme B S hS).map ko.left) ∧
      Surjective ((BigAffineFppf.toScheme B S hS).map ko.left) ∧
      LocallyOfFinitePresentation ((BigAffineFppf.toScheme B S hS).map ko.left) := by
    have hko : (BigAffineFppf.toScheme B S hS).map (sigmaDesc Y g).left =
        CategoryTheory.inv (sigmaCmp Y) ≫ Sigma.desc fun k ↦
          (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (g k).left) :=
      toScheme_map_sigma_desc Y _
    refine ⟨sigmaDesc Y g, sigmaι_sigmaDesc Y g, ?_, ?_, ?_⟩ <;> rw [hko]
    · have : Flat (Sigma.desc fun k ↦
          (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (g k).left)) :=
        hg.flat_sigmaDesc
      infer_instance
    · have : Surjective (Sigma.desc fun k ↦
          (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (g k).left)) :=
        hg.surjective_sigmaDesc
      infer_instance
    · have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
        HasRingHomProperty.instIsZariskiLocalAtSource
          (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
      have : LocallyOfFinitePresentation (Sigma.desc fun k ↦
          (BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map (g k).left)) :=
        IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) fun k ↦
          (hg.finite_presentation k).1
      infer_instance
  have hdcV := isDisjointCover_sigmaι.{u, w} Y
  -- lift classes over `∐ Y_k` are families of lift classes
  have hV := fun (s' : ∀ j : ULift.{w} (Fin n), P.presheaf.obj (op (Y j.down))) ↦
    P.existsUnique_of_isDisjointCover (fun j : ULift.{w} (Fin n) ↦ Y j.down)
      (fun j ↦ sigmaι Y j.down) hdcV s'
  obtain ⟨t₀, ht₀, -⟩ := hV (fun j ↦ s j.down)
  -- the double overlap
  obtain ⟨Pp, p₁, p₂, hp, hpb⟩ : ∃ (Pp : Over U') (p₁ p₂ : Pp ⟶ coprodOver Y), p₁ ≫ ko = p₂ ≫ ko ∧
      IsPullback ((BigAffineFppf.inclusion B S hS).map p₁.left)
        ((BigAffineFppf.inclusion B S hS).map p₂.left)
        ((BigAffineFppf.inclusion B S hS).map ko.left)
        ((BigAffineFppf.inclusion B S hS).map ko.left) :=
    ⟨_, _, _, pb_comm ko ko, isPullback_pb ko ko⟩
  -- two sections over `T` agreeing on all the pullbacks `T ×_{∐ Y_k} Y_l` agree
  have hext : ∀ {T : Over U'} (f : T ⟶ coprodOver Y) {t t' : P.presheaf.obj (op T)},
      (∀ l : ULift.{w} (Fin n), P.presheaf.map (pbFst f (sigmaι Y l.down)).op t =
        P.presheaf.map (pbFst f (sigmaι Y l.down)).op t') → t = t' := by
    intro T f t t' h
    obtain ⟨_, -, hu⟩ := P.existsUnique_of_isDisjointCover _ _
      (hdcV.of_isPullback ((BigAffineFppf.inclusion B S hS).map f.left)
        (fun j ↦ (BigAffineFppf.inclusion B S hS).map (pbFst f (sigmaι Y j.down)).left)
        (fun j ↦ (BigAffineFppf.inclusion B S hS).map (pbSnd f (sigmaι Y j.down)).left)
        (fun j ↦ isPullback_pb f (sigmaι Y j.down)))
      (fun j ↦ P.presheaf.map (pbFst f (sigmaι Y j.down)).op t)
    exact (hu _ fun j ↦ rfl).trans (hu _ fun j ↦ (h j).symm).symm
  have hclaim : P.presheaf.map p₁.op t₀ = P.presheaf.map p₂.op t₀ := by
    refine hext p₁ fun j ↦ hext (pbFst p₁ (sigmaι Y j.down) ≫ p₂) fun l ↦ ?_
    have e₁ := pb_comm (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down)
    have e₂ := pb_comm p₁ (sigmaι Y j.down)
    have hcomp := hs j.down l.down _
      (pbFst (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down) ≫ pbSnd p₁ (sigmaι Y j.down))
      (pbSnd (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down)) (by
        rw [← hιk j.down, ← hιk l.down, ← Category.assoc, Category.assoc _ _ (sigmaι Y j.down),
          ← e₂, ← Category.assoc (pbSnd _ _), ← e₁]
        simp only [Category.assoc, hp])
    have hL : P.presheaf.map (pbFst (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down)).op
        (P.presheaf.map (pbFst p₁ (sigmaι Y j.down)).op (P.presheaf.map p₂.op t₀)) =
        P.presheaf.map (pbSnd (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down)).op
          (s l.down) := by
      rw [← ht₀ l]
      simp only [← Functor.map_comp_apply, ← op_comp] at e₁ ⊢
      rw [e₁]
    have hR : P.presheaf.map (pbFst (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down)).op
        (P.presheaf.map (pbFst p₁ (sigmaι Y j.down)).op (P.presheaf.map p₁.op t₀)) =
        P.presheaf.map (pbFst (pbFst p₁ (sigmaι Y j.down) ≫ p₂) (sigmaι Y l.down) ≫
          pbSnd p₁ (sigmaι Y j.down)).op (s j.down) := by
      rw [← ht₀ j]
      simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc]
      rw [e₂]
    exact hR.trans (hcomp.trans hL.symm)
  obtain ⟨s₀, hs₀⟩ := P.exists_map_eq_of_fppf harr hi ko hkf hks hkp p₁ p₂ hp hpb t₀ hclaim
  refine ⟨s₀, fun k ↦ ?_, fun s₁ hs₁ ↦ ?_⟩
  · rw [← hιk k, op_comp, Functor.map_comp_apply, hs₀]
    exact ht₀ ⟨k⟩
  · refine P.injective_map_of_fppf harr hi ko hkf hks hkp ?_
    obtain ⟨_, -, huniq⟩ := hV (fun j ↦ s j.down)
    refine (huniq _ fun j ↦ ?_).trans (huniq _ fun j ↦ ?_).symm
    · rw [← Functor.map_comp_apply, ← op_comp, hιk]
      exact hs₁ j.down
    · rw [hs₀]
      exact ht₀ j

end LiftClassPresheaf

end Deformation.Artin.LiftClassSheaf

end
