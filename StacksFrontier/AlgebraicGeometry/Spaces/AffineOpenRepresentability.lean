module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluingBySize
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Representability over the affine opens of the base

Stacks 01JJ for the big fppf site of a scheme `S`, in the form in which it is applied to
isomorphism sheaves: an fppf sheaf `H` on the site is representable as soon as, for every affine
open `V` of `S`, the functor `T ↦ H(T) × Hom(T, V)` is represented — as tested on test objects with
affine underlying scheme only — by an object of the site of size at most that of `S`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.opensRestrictObj`: an open subscheme of the underlying scheme of
  an object of the big fppf site of `S`, as an object of that site.
* `AlgebraicGeometry.BigFppfOver.opensRestrictHom`: its open immersion, as a morphism of the site.

## Main results

* `AlgebraicGeometry.BigFppfOver.mem_topology_of_opensRestrictHom`: a sieve containing the open
  immersions of a family of opens covering an object is a covering sieve.
* `AlgebraicGeometry.Space.isRepresentable_of_isAffineOpen_represented`: Stacks 01JJ over the
  affine opens of the base.

## Implementation notes

Write `h_S` for the representable presheaf of the terminal object `S` of the site and `h_V` for
that of the open `V`. The comparison morphism from the representable of the given object `X_V`
to the fibre product `H ×_{h_S} h_V`, formed in presheaves, is a morphism of sheaves
(`AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj`); on an affine test object it is the
given bijection, because `h_S` has one section over every object, so it is an isomorphism by the
base's `AlgebraicGeometry.Space.isIso_of_bijective_app_of_isAffine`, and the chart `X_V ⟶ H` is
the base change of the open immersion `h_V ⟶ h_S`. The opens `V` cover `h_S` locally, since every
object of the site is covered by the preimages of the affine opens of `S`, and
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power` glues: the index type
`S.affineOpens` has cardinality at most `S.size` and every chart has size at most `S.size`, both
bounded by `S.size ^ ℵ₀`.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subscheme of the underlying scheme of an object `T` of the big fppf site of `S`,
regarded as an object of that site through the composite of its open immersion with the
structure morphism of `T`. -/
def opensRestrictObj (T : BigFppfOver B S hS) (U : ((toScheme B S hS).obj T).Opens) :
    BigFppfOver B S hS :=
  siteObject B S hS (contains_opens B T.left.property U) (U.ι ≫ T.hom.hom)

/-- The open immersion of an open subscheme of an object of the site, as a morphism of the
site. -/
def opensRestrictHom (T : BigFppfOver B S hS) (U : ((toScheme B S hS).obj T).Opens) :
    opensRestrictObj B S hS T U ⟶ T :=
  Over.homMk (ObjectProperty.homMk U.ι) (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying scheme of `AlgebraicGeometry.BigFppfOver.opensRestrictObj` is the open
subscheme. -/
theorem toScheme_obj_opensRestrictObj (T : BigFppfOver B S hS)
    (U : ((toScheme B S hS).obj T).Opens) :
    (toScheme B S hS).obj (opensRestrictObj B S hS T U) = U := rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.opensRestrictHom` is the
open immersion of the open subscheme. -/
theorem toScheme_map_opensRestrictHom (T : BigFppfOver B S hS)
    (U : ((toScheme B S hS).obj T).Opens) :
    (toScheme B S hS).map (opensRestrictHom B S hS T U) = U.ι := rfl

/-- **A sieve containing the open immersions of a covering family of opens is covering.** If
the opens `O i` of the underlying scheme of `T` cover it, every sieve on `T` containing all
`AlgebraicGeometry.BigFppfOver.opensRestrictHom` of the `O i` is a covering sieve of the fppf
topology. -/
theorem mem_topology_of_opensRestrictHom {T : BigFppfOver B S hS} {ι : Type*}
    (O : ι → ((toScheme B S hS).obj T).Opens) (hO : ∀ x, ∃ i, x ∈ O i) {R : Sieve T}
    (hR : ∀ i, R (opensRestrictHom B S hS T (O i))) : R ∈ topology B S hS T := by
  refine (topology B S hS).superset_covering ?_
    (ofArrows_mem_topology_of_isOpenImmersion B S hS (fun i => opensRestrictHom B S hS T (O i))
      (fun i => inferInstanceAs (IsOpenImmersion (O i).ι)) fun x => ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact hR i
  · obtain ⟨i, hi⟩ := hO x
    exact ⟨i, (Scheme.Opens.range_ι (O i)).symm ▸ hi⟩

end BigFppfOver

namespace Space

/-- The components of the canonical morphism into a pullback of presheaves of types are bijective
at `T` as soon as the pairing of the two legs is. -/
theorem bijective_app_pullback_lift {C : Type*} [Category* C] {P H K Y : Cᵒᵖ ⥤ Type u}
    (h : H ⟶ K) (c : Y ⟶ K) {p : P ⟶ H} {q : P ⟶ Y} (hw : p ≫ h = q ≫ c) (T : Cᵒᵖ)
    (hb : Function.Bijective fun z => (p.app T z, q.app T z)) :
    Function.Bijective ((pullback.lift p q hw).app T) := by
  have hsq := (IsPullback.of_hasPullback h c).map ((evaluation Cᵒᵖ (Type u)).obj T)
  have e1 : ∀ z, (pullback.fst h c).app T ((pullback.lift p q hw).app T z) = p.app T z :=
    fun z => congrArg (fun φ => φ.app T z) (pullback.lift_fst _ _ hw)
  have e2 : ∀ z, (pullback.snd h c).app T ((pullback.lift p q hw).app T z) = q.app T z :=
    fun z => congrArg (fun φ => φ.app T z) (pullback.lift_snd _ _ hw)
  refine ⟨fun a b hab => hb.1 ?_, fun z => ?_⟩
  · exact Prod.ext ((e1 a).symm.trans ((congrArg _ hab).trans (e1 b)))
      ((e2 a).symm.trans ((congrArg _ hab).trans (e2 b)))
  · obtain ⟨a, ha⟩ := hb.2 ((pullback.fst h c).app T z, (pullback.snd h c).app T z)
    exact ⟨a, Types.ext_of_isPullback hsq ((e1 a).trans (congrArg Prod.fst ha))
      ((e2 a).trans (congrArg Prod.snd ha))⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_AffineOpenRepresentability :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_AffineOpenRepresentability
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 01JJ over the affine opens of the base.** Let `H` be an fppf sheaf on the big fppf
site of `S`. Suppose that for every affine open `V` of `S` there are an object `X` of the site of
size at most that of `S`, a section `p` of `H` over `X` and a factorization `q` of `X ⟶ S`
through `V`, such that for every test object `T` with affine underlying scheme, composing with
`p` and `q` identifies the morphisms `T ⟶ X` with the pairs of a section of `H` over `T` and a
factorization of `T ⟶ S` through `V`. Then `H` is representable. -/
theorem isRepresentable_of_isAffineOpen_represented (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hloc : ∀ V : S.affineOpens, ∃ (X : BigFppfOver B S hS) (p : yoneda.obj X ⟶ H)
        (q : X ⟶ BigFppfOver.opensObj B S hS V.1),
        (∀ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          Function.Bijective (fun f : T ⟶ X =>
            ((⟨p.app (op T) f, f ≫ q⟩ : _ × (T ⟶ BigFppfOver.opensObj B S hS V.1))))) ∧
        ((BigFppfOver.toScheme B S hS).obj X).size ≤ S.size) :
    H.IsRepresentable := by
  choose X p q hbij hsize using hloc
  let top : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hterm : IsTerminal top := Over.mkIdTerminal
  let toTop : ∀ Z : BigFppfOver B S hS, Z ⟶ top := fun Z => Over.homMk Z.hom (Category.comp_id _)
  let K := yoneda.obj top
  let c : ∀ V : S.affineOpens, yoneda.obj (BigFppfOver.opensObj B S hS V.1) ⟶ K :=
    fun V => yoneda.map (toTop _)
  let h : H ⟶ K :=
    { app := fun T => ↾fun _ => toTop T.unop
      naturality := fun _ _ _ => by ext; exact hterm.hom_ext _ _ }
  -- the members of the covering family are relatively representable open immersions
  have hstable : (openImmersionOver B S hS).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  have hopen : ∀ V, (openImmersionOver B S hS).presheaf (c V) := fun V =>
    MorphismProperty.relative_map (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.1.ι))
  -- the affine opens of `S` cover `h_S`
  have hcov : (⨆ V, Subfunctor.range (c V)).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨T⟩ t -
    change (⨆ V, Subfunctor.range (c V)).sieveOfSection t ∈ BigFppfOver.topology B S hS T
    refine BigFppfOver.mem_topology_of_opensRestrictHom B S hS
      (fun V : S.affineOpens => T.hom.hom ⁻¹ᵁ V.1) (fun x => ?_) (fun V => ?_)
    · obtain ⟨W, hW, hxW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := T.hom.hom x) (by trivial)
      exact ⟨⟨W, hW⟩, hxW⟩
    · change K.map _ t ∈ (⨆ V, Subfunctor.range (c V)).obj _
      rw [Subfunctor.iSup_obj]
      refine Set.mem_iUnion.2 ⟨V, BigFppfOver.homOfRangeLe B S hS V.1 ?_, hterm.hom_ext _ _⟩
      rintro _ ⟨y, rfl⟩
      exact y.2
  -- each chart is the base change of the open immersion `h_V ⟶ h_S`
  have hp : ∀ V, IsPullback (p V) (yoneda.map (q V)) h (c V) := by
    intro V
    have hw : p V ≫ h = yoneda.map (q V) ≫ c V := by ext T x; exact hterm.hom_ext _ _
    let l := pullback.lift (p V) (yoneda.map (q V)) hw
    have hl : IsIso l :=
      isIso_of_bijective_app_of_isAffine (BigFppfOver.isSheaf_yoneda_obj B S hS _)
        (BigFppfOver.isSheaf_pullback_yoneda_obj h (c V) hH
          (BigFppfOver.isSheaf_yoneda_obj B S hS top)) l
        fun T hT => bijective_app_pullback_lift h (c V) hw (op T) (hbij V T hT)
    exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso l) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  exact isRepresentable_of_locally_covering_of_le_power B S hS c hcov hopen ⟨H, hH⟩ h p
    (fun V => yoneda.map (q V)) hp hS
    (S.mk_affineOpens_le_size.trans (self_le_power _ one_le_aleph0))
    (fun V => (hsize V).trans (self_le_power _ one_le_aleph0))

end Space

end AlgebraicGeometry
