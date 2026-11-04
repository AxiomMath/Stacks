module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianSmallSubpresheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines

/-!
# A separator for the quasi-coherent modules on a category fibred in groupoids

Let `𝒳` be an essentially small category fibred in groupoids over the big fppf site of `S`, for
instance an algebraic stack.  This file proves that `QCoh(𝒪_𝒳)` has a separator, the input of the
special adjoint functor theorem that the coherator of **Stacks 0778** and **Stacks 0781**
part (2) needs and that the source draws from the Grothendieck property, **Stacks 0781**
part (1).

## The argument

A quasi-coherent module `F` restricts to a cartesian presheaf of modules on the affine objects of
`𝒳` (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`).  Every
section of it at an affine object lies in a cartesian sub-presheaf of cardinality bounded by a
cardinal `AlgebraicGeometry.FibredSite.affineBound` depending only on `𝒳`
(`Stacks.PresheafOfModules.exists_small_cartesian_submodule`).  A cartesian presheaf of modules on
the affine objects is the restriction of a quasi-coherent module on `𝒳` (**Stacks 0H0E**, through
the equivalence of **Stacks 0H0B** and **Stacks 0H0C**), and its inclusion into the restriction of
`F` is the restriction of a morphism to `F`.  So the bounded quasi-coherent modules separate.

The source argues through a smooth groupoid presentation `𝒳 = [U/R]` and the bounded generation
of quasi-coherent modules on a flat groupoid (Groupoids in Spaces, Lemma 0780).  The argument here
needs no presentation: the cartesian sub-presheaves are closed under the purity witnesses of every
arrow between affine objects, flat or not, which is what makes them quasi-coherent.

## Main definitions

* `AlgebraicGeometry.FibredSite.affineRep`: a set of representatives of the affine objects.
* `AlgebraicGeometry.FibredSite.affineBound`: the cardinal bound.
* `AlgebraicGeometry.FibredSite.IsAffineBounded`: the bounded quasi-coherent modules.

## Main results

* `AlgebraicGeometry.FibredSite.exists_isAffineBounded_hom`: every section of a quasi-coherent
  module over a representative affine object is hit by a bounded quasi-coherent module.
* `AlgebraicGeometry.FibredSite.isSeparating_isAffineBounded`: the bounded quasi-coherent
  modules are separating.
* `AlgebraicGeometry.FibredSite.hasSeparator_quasicoherentModules_of_essentiallySmall`: a
  separator, once the bounded quasi-coherent modules are known to form an essentially small
  class.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 0780](https://stacks.math.columbia.edu/tag/0780)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.FibredSite

open Stack Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The commutative ring presheaf of functions on the affine objects of `𝒳`. -/
abbrev affineRing : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Stack.AffineCategory.toScheme B S hS p).op ⋙ Scheme.Γ

/-- The category of affine objects of `𝒳` is essentially small. -/
theorem essentiallySmall_affineCategory : EssentiallySmall.{u} (AffineCategory B S hS p) :=
  CategoryTheory.essentiallySmall_fullSubcategory _

/-- The index type of a set of representatives of the affine objects of `𝒳`. -/
abbrev AffineRep : Type u :=
  haveI := essentiallySmall_affineCategory B S hS p
  Shrink.{u} (Skeleton (AffineCategory B S hS p)ᵒᵖ)

/-- A set of representatives of the affine objects of `𝒳`, up to isomorphism. -/
noncomputable def affineRep (i : AffineRep B S hS p) : (AffineCategory B S hS p)ᵒᵖ :=
  haveI := essentiallySmall_affineCategory B S hS p
  (fromSkeleton _).obj ((equivShrink _).symm i)

/-- Every affine object of `𝒳` is isomorphic to one of the representatives
`AlgebraicGeometry.FibredSite.affineRep`. -/
theorem exists_affineRep_iso (X : (AffineCategory B S hS p)ᵒᵖ) :
    ∃ i, Nonempty (affineRep B S hS p i ≅ X) := by
  have := essentiallySmall_affineCategory B S hS p
  refine ⟨equivShrink _ (toSkeleton X), ⟨?_⟩⟩
  simpa only [affineRep, Equiv.symm_apply_apply] using fromSkeletonToSkeletonIso X

/-- The cardinal bound of the separating family: it dominates the number of representatives, the
rings of functions at the representatives, and the arrows between them. -/
noncomputable def affineBound : Cardinal.{u} :=
  max ℵ₀ (#(AffineRep B S hS p) + #(Σ i, (affineRing B S hS p).obj (affineRep B S hS p i)) +
    #(Σ ij : AffineRep B S hS p × AffineRep B S hS p,
      affineRep B S hS p ij.1 ⟶ affineRep B S hS p ij.2))

/-- The cardinal bound `AlgebraicGeometry.FibredSite.affineBound` is infinite. -/
theorem aleph0_le_affineBound : ℵ₀ ≤ affineBound B S hS p := le_max_left _ _

/-- The number of representatives of the affine objects is at most
`AlgebraicGeometry.FibredSite.affineBound`. -/
theorem mk_affineRep_le : #(AffineRep B S hS p) ≤ affineBound B S hS p :=
  (le_self_add.trans le_self_add).trans (le_max_right _ _)

/-- The ring of functions at each representative affine object has cardinality at most
`AlgebraicGeometry.FibredSite.affineBound`. -/
theorem mk_affineRing_le (i : AffineRep B S hS p) :
    #((affineRing B S hS p).obj (affineRep B S hS p i)) ≤ affineBound B S hS p :=
  ((mk_le_of_injective (f := fun x => (⟨i, x⟩ : Σ i, (affineRing B S hS p).obj
    (affineRep B S hS p i))) fun _ _ h => eq_of_heq (Sigma.mk.inj h).2).trans
    (le_add_self.trans le_self_add)).trans (le_max_right _ _)

/-- The set of arrows between two representative affine objects has cardinality at most
`AlgebraicGeometry.FibredSite.affineBound`. -/
theorem mk_affineRep_hom_le (i j : AffineRep B S hS p) :
    #(affineRep B S hS p i ⟶ affineRep B S hS p j) ≤ affineBound B S hS p :=
  ((mk_le_of_injective (f := fun x => (⟨(i, j), x⟩ : Σ ij : AffineRep B S hS p ×
    AffineRep B S hS p, affineRep B S hS p ij.1 ⟶ affineRep B S hS p ij.2))
    fun _ _ h => eq_of_heq (Sigma.mk.inj h).2).trans le_add_self).trans (le_max_right _ _)

/-- A quasi-coherent module is *bounded* when its sections over the representatives of the affine
objects have cardinality at most `AlgebraicGeometry.FibredSite.affineBound`. -/
def IsAffineBounded : ObjectProperty (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  fun G => ∀ i, #(G.obj.val.obj (op (affineRep B S hS p i).unop.obj)) ≤ affineBound B S hS p

/-- **Every section of a quasi-coherent module over a representative affine object is hit by a
bounded quasi-coherent module.**  The restriction of `F` to the affine objects is a cartesian
presheaf of modules, so the section lies in a cartesian sub-presheaf of bounded cardinality; that
sub-presheaf is a sheaf for the fppf topology by faithfully flat descent and quasi-coherent there,
hence the restriction of a quasi-coherent module `G` on `𝒳` (Stacks 0H0B, 0H0C, 0H0E), and the
inclusion of the sub-presheaf is the restriction of a morphism `G ⟶ F`. -/
theorem exists_isAffineBounded_hom (F : quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
    (i : AffineRep B S hS p) (s : F.obj.val.obj (op (affineRep B S hS p i).unop.obj)) :
    ∃ (G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp) (_ : IsAffineBounded B S hS p hp G)
      (g : G ⟶ F) (t : G.obj.val.obj (op (affineRep B S hS p i).unop.obj)),
      g.hom.val.app _ t = s := by
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := isEquivalence_moduleRestriction B S hS p hp (siteKindRingedSite B S hS p hp .fppf).J
    (BigFppfOver.associatedTopology B S hS p .fppf)
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
  let Res := Stacks.DenseSubsiteModules.moduleRestriction (siteKindRingedSite B S hS p hp .fppf).J
    (BigFppfOver.associatedTopology B S hS p .fppf) (Stack.AffineCategory.inclusion B S hS p)
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
  let M : PresheafOfModules.{u} (affineRing B S hS p ⋙ forget₂ CommRingCat RingCat) :=
    (PresheafOfModules.pushforward₀ (Stack.AffineCategory.inclusion B S hS p) _).obj F.obj.val
  have hM : ∀ {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} M f) :=
    fun {X Y} f =>
      FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite F.obj F.property
        f.unop.hom Y.unop.property X.unop.property
  obtain ⟨K, hsK, hKb, hKc⟩ := Stacks.PresheafOfModules.exists_small_cartesian_submodule M hM
    (affineRep B S hS p) (exists_affineRep_iso B S hS p) (aleph0_le_affineBound B S hS p)
    (mk_affineRep_le B S hS p) (mk_affineRing_le B S hS p) (mk_affineRep_hom_le B S hS p) i s
  let N : SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (Stack.AffineCategory.inclusion B S hS p)
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :=
    ⟨K.toPresheafOfModules, isSheaf_of_cartesian B S hS p (affineRing B S hS p) rfl hp .fppf
      K.toPresheafOfModules fun f => hKc f⟩
  let e := Res.objObjPreimageIso N
  let G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
    ⟨Res.objPreimage N, isQuasicoherentOnSite_of_moduleRestriction B S hS p _ _ hp _ _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
        (Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
          (siteKindRingedSite B S hS p hp .fppf) N fun _ _ f => hKc f.op))⟩
  let ι : N ⟶ Res.obj F.obj := ⟨K.ι⟩
  let g₀ : Res.objPreimage N ⟶ F.obj := Res.preimage (e.hom ≫ ι)
  refine ⟨G, fun j => ?_, ObjectProperty.homMk g₀,
    (e.inv.val.app (affineRep B S hS p i) ⟨s, hsK⟩ : (Res.obj G.obj).val.obj _), ?_⟩
  · have h := fun z => ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.val.app (affineRep B S hS p j)) e.hom_inv_id) z
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, SheafOfModules.id_val,
      PresheafOfModules.id_app, ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
    have hinj : Function.Injective (e.hom.val.app (affineRep B S hS p j)) :=
      fun x y hxy => (h x).symm.trans ((congrArg _ hxy).trans (h y))
    exact (mk_le_of_injective hinj).trans (hKb j)
  · have h2 := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.val.app (affineRep B S hS p i)) e.inv_hom_id) ⟨s, hsK⟩
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      SheafOfModules.id_val, PresheafOfModules.id_app] at h2
    show (Res.map g₀).val.app (affineRep B S hS p i) _ = s
    rw [show Res.map g₀ = e.hom ≫ ι from Res.map_preimage _]
    show (ι.val.app (affineRep B S hS p i)) ((e.hom.val.app (affineRep B S hS p i))
      ((e.inv.val.app (affineRep B S hS p i)) ⟨s, hsK⟩)) = s
    exact congrArg (ι.val.app (affineRep B S hS p i)) h2

/-- **The bounded quasi-coherent modules are separating.**  Two morphisms `φ ψ : F ⟶ F'` of
quasi-coherent modules which agree after composition with every morphism from a bounded
quasi-coherent module agree on every section over a representative affine object, by
`AlgebraicGeometry.FibredSite.exists_isAffineBounded_hom`; they then agree on every section over
an affine object, by naturality along the isomorphisms to the representatives, and so are equal,
the restriction to the affine objects being faithful (**Stacks 0H0B**). -/
theorem isSeparating_isAffineBounded : (IsAffineBounded B S hS p hp).IsSeparating := by
  intro F F' φ ψ h
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  let Res := Stacks.DenseSubsiteModules.moduleRestriction (siteKindRingedSite B S hS p hp .fppf).J
    (BigFppfOver.associatedTopology B S hS p .fppf) (Stack.AffineCategory.inclusion B S hS p)
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
  have hrep : ∀ (i : AffineRep B S hS p) (x : F.obj.val.obj (op (affineRep B S hS p i).unop.obj)),
      φ.hom.val.app _ x = ψ.hom.val.app _ x := by
    intro i x
    obtain ⟨G, hG, g, t, rfl⟩ := exists_isAffineBounded_hom B S hS p hp F i x
    exact congrArg (fun k : G ⟶ F' => k.hom.val.app (op (affineRep B S hS p i).unop.obj) t)
      (h G hG g)
  refine ObjectProperty.hom_ext _ (Res.map_injective (SheafOfModules.hom_ext ?_))
  ext X x
  obtain ⟨i, ⟨e⟩⟩ := exists_affineRep_iso B S hS p X
  have hx : x = (Res.obj F.obj).val.map e.hom ((Res.obj F.obj).val.map e.inv x) := by
    rw [← PresheafOfModules.map_comp_apply, e.inv_hom_id, PresheafOfModules.map_id]
    rfl
  refine (congrArg ((Res.map φ.hom).val.app X) hx).trans ?_
  refine Eq.trans ?_ (congrArg ((Res.map ψ.hom).val.app X) hx).symm
  refine (PresheafOfModules.naturality_apply (Res.map φ.hom).val e.hom _).trans ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply (Res.map ψ.hom).val e.hom _).symm
  exact congrArg _ (hrep i _)

/-- **`QCoh(𝒪_𝒳)` has a separator**, granted that the bounded quasi-coherent modules form an
essentially small class: the coproduct of a small set of representatives of them. -/
theorem hasSeparator_quasicoherentModules_of_essentiallySmall
    (hsmall : ObjectProperty.EssentiallySmall.{u} (IsAffineBounded B S hS p hp)) :
    HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) := by
  classical
  let C := quasicoherentModules.{u, u + 1, u, u} B S hS p hp
  have : HasColimitsOfSize.{u, u} C := hasColimitsOfSize_quasicoherentModules B S hS p hp
    (closedUnderColimitsOfSize_quasicoherentModules B S hS p hp)
  obtain ⟨Q, _, -, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u}
    (IsAffineBounded B S hS p hp)
  have hQsep : Q.IsSeparating := by
    intro X₁ X₂ f g hfg
    apply ObjectProperty.IsSeparating.of_le (isSeparating_isAffineBounded B S hS p hp) hPQ f g
    rintro Y ⟨Z, hZ, ⟨e⟩⟩ k
    simpa using congrArg (fun t ↦ e.hom ≫ t) (hfg Z hZ (e.inv ≫ k))
  let β := Shrink.{u} (Subtype Q)
  let f : β → C := fun b ↦ ((equivShrink.{u} (Subtype Q)).symm b).1
  have hOf : Q ≤ ObjectProperty.ofObj f := by
    intro A hA
    apply (ObjectProperty.ofObj_iff f A).2
    refine ⟨equivShrink.{u} (Subtype Q) ⟨A, hA⟩, ?_⟩
    simp [f]
  exact ⟨∐ f, (isSeparator_sigma f).2 (ObjectProperty.IsSeparating.of_le hQsep hOf)⟩

end AlgebraicGeometry.FibredSite

end
