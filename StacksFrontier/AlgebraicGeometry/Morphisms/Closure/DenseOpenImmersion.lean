module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense

/-!
# Scheme-theoretically dense open immersions

An open immersion of schemes has scheme-theoretically dense image exactly when the natural map
from the structure sheaf of the target to the direct image of the structure sheaf of the source
is injective.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono` characterizes
  scheme-theoretic density of the image of an open immersion by injectivity of its
  structure-sheaf map.

## Implementation notes

The image of an open immersion `j` is `j.opensRange`, and the map `𝒪_X ⟶ j_* 𝒪_U` is the natural
transformation `j.c` on underlying presheaves; being a monomorphism expresses injectivity of this
sheaf map.

The proof reduces both sides to injectivity of the maps `f.app V` on sections, where the open `V`
may be taken affine: for the structure-sheaf map this is
`CategoryTheory.NatTrans.mono_iff_mono_app` together with sheaf-theoretic descent from
affine opens, and for scheme-theoretic density it is the vanishing of the kernel ideal sheaf,
which `AlgebraicGeometry.Scheme.ker_of_isAffine` reads off from the sections over an affine open.
The two descriptions are matched by identifying the two ways of intersecting two open
subschemes, which differ by the canonical isomorphism between the two inverse images.

## References

* [Stacks Project, Tag 01RE](https://stacks.math.columbia.edu/tag/01RE)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- Postcomposing a ring map with an isomorphism does not change whether it is injective. -/
private lemma injective_comp_iso_iff {R S T : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T)
    (hb : IsIso b) : Function.Injective (a ≫ b).hom ↔ Function.Injective a.hom :=
  (ConcreteCategory.bijective_of_isIso b).1.of_comp_iff a.hom

private lemma app_injective_congr_opens {A B : Scheme.{u}} (f : A ⟶ B) (V W : B.Opens)
    (h : V = W) :
    Function.Injective (f.app V).hom ↔ Function.Injective (f.app W).hom := by
  rw [h]

/-- The two inverse images of two open subschemes have the same range in the ambient scheme. -/
lemma range_preimage_ι_comp_ι {X : Scheme.{u}} (U V : X.Opens) :
    Set.range ⇑((U.ι ⁻¹ᵁ V).ι ≫ U.ι) = Set.range ⇑((V.ι ⁻¹ᵁ U).ι ≫ V.ι) := by
  have hI : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V.ι ''ᵁ (V.ι ⁻¹ᵁ U) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_comm _ _
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
    Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hI]

/-- Sections of the inclusion of an open subscheme over a second open subscheme are the global
sections of the intersection, viewed inside the second open subscheme. -/
public lemma app_injective_iff_appTop_inter {X : Scheme.{u}} (U V : X.Opens) :
    Function.Injective (U.ι.app V).hom ↔
      Function.Injective (((V.ι ⁻¹ᵁ U).ι).appTop).hom := by
  let p := (U.ι ⁻¹ᵁ V).ι
  let q := (V.ι ⁻¹ᵁ U).ι
  have hrange : Set.range ⇑(p ≫ U.ι) = Set.range ⇑(q ≫ V.ι) := range_preimage_ι_comp_ι U V
  let e := IsOpenImmersion.isoOfRangeEq (p ≫ U.ι) (q ≫ V.ι) hrange
  have hcomp : p ≫ U.ι = e.hom ≫ q ≫ V.ι :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac (p ≫ U.ι) (q ≫ V.ι) hrange).symm
  have happ := Scheme.Hom.congr_app hcomp V
  simp only [Scheme.Hom.comp_app] at happ
  let W₁ := U.ι ⁻¹ᵁ V
  let a := U.ι.app V
  let b := p.app W₁
  let c := V.ι.app V
  let d := q.app (V.ι ⁻¹ᵁ V)
  let g := e.hom.app ((q ≫ V.ι) ⁻¹ᵁ V)
  have hpre : (p ≫ U.ι) ⁻¹ᵁ V = (e.hom ≫ q ≫ V.ι) ⁻¹ᵁ V :=
    congrArg (fun f : _ ⟶ X => f ⁻¹ᵁ V) hcomp
  let t := W₁.toScheme.presheaf.map (eqToHom hpre).op
  have hb : IsIso b := by
    change IsIso (p.app W₁)
    apply Scheme.Hom.isIso_app p W₁
    rw [show p.opensRange = W₁ by simp [p, W₁]]
  have hc : IsIso c := by
    change IsIso (V.ι.app V)
    apply Scheme.Hom.isIso_app V.ι V
    rw [Scheme.Opens.opensRange_ι]
  have hg : IsIso g := inferInstanceAs (IsIso (e.hom.app ((q ≫ V.ι) ⁻¹ᵁ V)))
  have ht : IsIso t := (W₁.toScheme.presheaf.mapIso (eqToIso hpre).op).isIso_hom
  have happ' : a ≫ b = ((c ≫ d) ≫ g) ≫ t := by
    simpa [a, b, c, d, g, t, W₁, p, q] using happ
  have hinj : Function.Injective a.hom ↔ Function.Injective d.hom :=
    (injective_comp_iso_iff a b hb).symm.trans <| by
      rw [happ']
      exact ((injective_comp_iso_iff _ t ht).trans (injective_comp_iso_iff _ g hg)).trans
        (Function.Injective.of_comp_iff' _ (ConcreteCategory.bijective_of_isIso c))
  exact hinj.trans (app_injective_congr_opens q _ _ (by ext; simp))

/-- The kernel ideal sheaf of a morphism of schemes vanishes as soon as the map on sections over
every affine open of the target is injective. -/
public lemma ker_eq_bot_of_app_injective_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ W : Y.affineOpens, Function.Injective (f.app W).hom) : f.ker = ⊥ :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (fun W : Y.affineOpens => W)
    (iSup_affineOpens_eq_top Y) fun W => le_antisymm ((Scheme.Hom.ideal_ker_le f W).trans_eq
      ((RingHom.injective_iff_ker_eq_bot _).mp (h W))) bot_le

/-- The structure-sheaf map of a morphism of schemes is a monomorphism exactly when it is
injective on the sections over every open subscheme of the target. -/
public lemma mono_c_iff_app_injective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono f.c ↔ ∀ V : Y.Opens, Function.Injective (f.app V).hom := by
  rw [NatTrans.mono_iff_mono_app]
  exact ⟨fun h V => (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp (h (.op V)),
    fun h V => (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr (h V.unop)⟩

/-- Injectivity of the maps on sections over all affine opens gives injectivity over every
open. -/
lemma app_injective_of_app_injective_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ W : Y.affineOpens, Function.Injective (f.app W).hom) (V : Y.Opens) :
    Function.Injective (f.app V).hom := by
  intro s t hst
  apply Y.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨W, hWV, hxW, ?_⟩
  apply h ⟨W, hW⟩
  let i : Opposite.op V ⟶ Opposite.op W := (homOfLE hWV).op
  let rY := Y.presheaf.map i
  let rX := X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i.unop).op
  have hn (z) : (f.app W).hom (rY.hom z) = rX.hom ((f.app V).hom z) := by
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun k => k.hom z) (f.naturality i)
  exact (hn s).trans ((congrArg rX.hom hst).trans (hn t).symm)

/-- Over an affine target, scheme-theoretic dominance is injectivity on global sections. -/
lemma isSchemeTheoreticallyDominant_iff_appTop_injective_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    IsSchemeTheoreticallyDominant f ↔ Function.Injective f.appTop.hom := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine, RingHom.injective_iff_ker_eq_bot]
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.ext_of_isAffine (by simpa using h)⟩
  simpa using congrArg (fun J : Y.IdealSheafData => J.ideal ⟨⊤, isAffineOpen_top Y⟩) h

private lemma app_injective_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : U.toScheme.Opens) :
    Function.Injective ((f ∣_ U).app V).hom ↔
      Function.Injective (f.app (U.ι ''ᵁ V)).hom := by
  rw [morphismRestrict_app]
  exact injective_comp_iso_iff _ _
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V)).op).isIso_hom

private lemma app_injective_iso_precomp_iff {A B C : Scheme.{u}}
    (e : A ≅ B) (f : B ⟶ C) (V : C.Opens) :
    Function.Injective ((e.hom ≫ f).app V).hom ↔ Function.Injective (f.app V).hom := by
  rw [Scheme.Hom.comp_app]
  exact injective_comp_iso_iff (f.app V) (e.hom.app _) inferInstance

private lemma app_injective_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B}
    (h : f = g) (V : B.Opens) :
    Function.Injective (f.app V).hom ↔ Function.Injective (g.app V).hom := by
  rw [h]

/-- The two ways of intersecting two open subschemes agree, compatibly with the inclusions. -/
private lemma exists_iso_preimage_comp_ι {X : Scheme.{u}} (R V : X.Opens) :
    ∃ e : (R.ι ⁻¹ᵁ V).toScheme ≅ (V.ι ⁻¹ᵁ R).toScheme,
      e.hom ≫ (V.ι ⁻¹ᵁ R).ι = R.ι ∣_ V := by
  have h₁ := (isPullback_morphismRestrict V.ι R).flip
  have h₂ := isPullback_morphismRestrict R.ι V
  refine ⟨h₂.isoPullback ≪≫ h₁.isoPullback.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    h₁.isoPullback_inv_fst, h₂.isoPullback_hom_fst]

/-- An open immersion has scheme-theoretically dense image if and only if its structure-sheaf
map is injective. -/
@[stacks 01RE]
public theorem isSchemeTheoreticallyDense_opensRange_iff_mono
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ↔ Mono j.c := by
  let R : X.Opens := j.opensRange
  let i : R.toScheme ⟶ X := R.ι
  have hfactor : j.isoOpensRange.hom ≫ i = j := by simp [i, R]
  have hji (V : X.Opens) :
      Function.Injective (j.app V).hom ↔ Function.Injective (i.app V).hom :=
    (app_injective_congr_hom hfactor V).symm.trans (app_injective_iso_precomp_iff _ _ V)
  refine ⟨fun hdense => ?_, fun hmono V => ?_⟩
  · refine (mono_c_iff_app_injective j).2 (app_injective_of_app_injective_affine j fun W => ?_)
    rw [hji, app_injective_iff_appTop_inter R W.1]
    exact (isSchemeTheoreticallyDominant_iff_appTop_injective_of_isAffine _).mp (hdense W.1)
  · refine (isSchemeTheoreticallyDominant_iff _).2
      (ker_eq_bot_of_app_injective_affine _ fun W => ?_)
    obtain ⟨e, he⟩ := exists_iso_preimage_comp_ι R V
    exact (app_injective_iso_precomp_iff e _ W.1).mp ((app_injective_congr_hom he W.1).mpr
      ((app_injective_morphismRestrict_iff i V W.1).mpr
        ((hji _).mp ((mono_c_iff_app_injective j).mp hmono _))))

end AlgebraicGeometry

end
