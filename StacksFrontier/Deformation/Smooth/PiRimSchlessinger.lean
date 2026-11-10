module

public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.Smooth.Pi

/-!
# Products over the base: the Rim-Schlessinger condition

A product over `𝒞_Λ` of a family of deformation categories is again a deformation category.
Condition (RS) concerns one cospan at a time, and a cospan in the product over the base is a
cospan of Artinian bases together with one cospan in each factor lying over it. Its fibre product
is assembled from the fibre product of the bases, which exists because one leg of the base cospan
is surjective, together with one fibre product in each factor, which (RS) in that factor supplies
over the base one; and (RS) in the factors also says that each of those stays a fibre product in
the base, which is what makes the assembled cone a fibre product and keeps it one in the base.

This is what the chain of **Stacks 0DZF** needs. That chain passes through the finite products
`∏ 𝓓_{P_{𝔪 i}}`, `∏ 𝓓_{P^h_{𝔪 i}}` and `∏ 𝓓_{P^∧_{𝔪 i}}` of deformation categories, and the
smoothness criterion of **Stacks 0DYP**,
`Deformation.isSmooth_iff_differential_surjective_and_lifts`, is available only at a *deformation*
category: it takes `Deformation.IsDeformationCategory` for both its source and its target. The
results here are what discharge that hypothesis at the products, and so make the criterion
applicable to the three maps of the chain.

## Main results

* `Deformation.surjective_map_of_isHomLift`: a morphism lying over a surjection of Artinian local
  algebras has surjective image.
* `Deformation.exists_pullbackCone_with_base`: under (RS), a cospan whose second leg lies over a
  surjection has a fibre product whose image is *the given* limiting cone in the base, not merely
  a cone isomorphic to it.
* `Deformation.piBasedCategory_satisfiesRS`: a product over the base of categories satisfying (RS)
  satisfies (RS).
* `Deformation.piBasedCategory_isDeformationCategory`: a product over the base of deformation
  categories is a deformation category.

## Implementation notes

`Deformation.exists_pullbackCone_with_base` is stated with the base cone fixed in advance because
the factors of a product must be assembled over *one* base object: condition (RS) only produces
some fibre product in a factor, whose image is then merely isomorphic to the chosen base fibre
product, and the factor cone has to be transported along that isomorphism before the factors can
be put together. The transport is along a lift of the comparison isomorphism, which is invertible
because a lift of an isomorphism in a category cofibered in groupoids is one.

The two pieces of the proof that are long enough to elaborate slowly on their own — the
construction of a factor cone over the chosen base cone, and the verification that the morphism
induced into the assembled cone lies over the morphism induced into the base cone — are isolated
as `Deformation.exists_pullbackCone_component` and `Deformation.isHomLift_of_pullback_fac`. The
latter is stated for arbitrary cones and arbitrary factorizations through them, so that it does
not mention the product at all.

The product statements are proved for `Deformation.PiOver.structureFunctor` and then read off for
`Deformation.piBasedCategory`, which is that functor packaged as a based category: inside the
proof every object is an honest `Deformation.PiOver` and every projection is available, while the
unfolding of `(Deformation.piBasedCategory 𝓖).obj` is only needed once, at the statement.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06J9](https://stacks.math.columbia.edu/tag/06J9)
* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uι u w v₁ u₁ v₂ u₂

namespace Deformation

/-- A lift through the opposite functor is a lift through the functor itself. -/
private theorem isHomLift_unop
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (p : 𝒟 ⥤ 𝒞) {A B : 𝒞ᵒᵖ} {X Y : 𝒟ᵒᵖ} {f : A ⟶ B} {g : X ⟶ Y}
    (h : p.op.IsHomLift f g) : p.IsHomLift f.unop g.unop := by
  cases h
  exact IsHomLift.map _ _

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism lying over a surjection of Artinian local algebras has surjective image: the
image is the surjection itself. -/
public theorem surjective_map_of_isHomLift
    {F : Type u₂} [Category.{v₂} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} {X Y : F} (f : A ⟶ B) (g : X ⟶ Y)
    (h : p.IsHomLift f g) (hf : Function.Surjective f.hom) :
    Function.Surjective (p.map g).hom := by
  cases h
  exact hf

/-- **A fibre product over a prescribed cone in the base.** Under condition (RS), a cospan whose
second leg lies over a surjection has a fibre product whose image is the *given* limiting cone
`c₀` in the base: condition (RS) produces a fibre product whose image is only isomorphic to `c₀`,
and the comparison isomorphism is then lifted and inverted, which is possible because a lift of
an isomorphism in a category cofibered in groupoids is an isomorphism. -/
public theorem exists_pullbackCone_with_base
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : SatisfiesRS 𝓖.p)
    {X Y Z : 𝓖.obj} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : Function.Surjective (𝓖.p.map g).hom)
    (c₀ : PullbackCone (𝓖.p.map f) (𝓖.p.map g)) (hc₀ : IsLimit c₀) :
    ∃ (c : PullbackCone f g) (hc : 𝓖.p.obj c.pt = c₀.pt),
      Nonempty (IsLimit c) ∧
      𝓖.p.map c.fst = eqToHom hc ≫ c₀.fst ∧
      𝓖.p.map c.snd = eqToHom hc ≫ c₀.snd := by
  classical
  obtain ⟨d, ⟨hd⟩, ⟨hd₀⟩⟩ := hG.2 f g hg
  let e : 𝓖.p.obj d.pt ≅ c₀.pt := hd₀.conePointUniqueUpToIso hc₀
  obtain ⟨y, a, ha⟩ := hG.1.exists_lift e.hom.op (Opposite.op d.pt) rfl
  have := hG.1.isStronglyCartesian_homLift e.hom.op a
  have : IsIso a := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝓖.p.op e.hom.op a
  let b := a.unop
  have : IsIso b := inferInstanceAs (IsIso a.unop)
  have hb : 𝓖.p.IsHomLift e.hom b := isHomLift_unop 𝓖.p ha
  have hy : 𝓖.p.obj y.unop = c₀.pt := IsHomLift.codomain_eq 𝓖.p e.hom b
  have hbmap : 𝓖.p.map b = e.hom ≫ eqToHom hy.symm := by
    have h := IsHomLift.fac' 𝓖.p e.hom b
    change 𝓖.p.map b = eqToHom rfl ≫ e.hom ≫ eqToHom hy.symm at h
    simpa only [eqToHom_refl, Category.id_comp] using h
  have hbimap : 𝓖.p.map (inv b) = eqToHom hy ≫ e.inv := by
    apply (cancel_epi (𝓖.p.map b)).mp
    rw [← 𝓖.p.map_comp, IsIso.hom_inv_id, 𝓖.p.map_id, hbmap]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.hom_inv_id]
  let c : PullbackCone f g := PullbackCone.mk (inv b ≫ d.fst) (inv b ≫ d.snd)
    (by simp only [Category.assoc, d.condition])
  have hcd : c ≅ d := PullbackCone.ext (asIso b).symm rfl rfl
  refine ⟨c, hy, ⟨IsLimit.ofIsoLimit hd hcd.symm⟩, ?_, ?_⟩
  · change 𝓖.p.map (inv b ≫ d.fst) = _
    rw [𝓖.p.map_comp, hbimap, Category.assoc]
    exact eqToHom hy ≫= hd₀.conePointUniqueUpToIso_inv_comp hc₀ WalkingCospan.left
  · change 𝓖.p.map (inv b ≫ d.snd) = _
    rw [𝓖.p.map_comp, hbimap, Category.assoc]
    exact eqToHom hy ≫= hd₀.conePointUniqueUpToIso_inv_comp hc₀ WalkingCospan.right

/-- One factor of the fibre product of a cospan in a product over the base: a cospan lying over a
cospan of bases whose second leg is surjective has, in each factor satisfying (RS), a fibre
product lying over the chosen fibre product of the bases. -/
private theorem exists_pullbackCone_component
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : SatisfiesRS 𝓖.p)
    {xb yb zb : ArtinianLocalAlgCat.{u, w, w} Λ k} {fb : xb ⟶ zb} {gb : yb ⟶ zb}
    {c₀ : PullbackCone fb gb} (hc₀ : IsLimit c₀) (hgb : Function.Surjective gb.hom)
    {X Y Z : 𝓖.obj} (hX : 𝓖.p.obj X = xb) (hY : 𝓖.p.obj Y = yb) (hZ : 𝓖.p.obj Z = zb)
    (f : X ⟶ Z) (g : Y ⟶ Z) (hf : 𝓖.p.IsHomLift fb f) (hgl : 𝓖.p.IsHomLift gb g) :
    ∃ (c : PullbackCone f g) (hc : 𝓖.p.obj c.pt = c₀.pt),
      Nonempty (IsLimit c) ∧
      𝓖.p.map c.fst = eqToHom hc ≫ c₀.fst ≫ eqToHom hX.symm ∧
      𝓖.p.map c.snd = eqToHom hc ≫ c₀.snd ≫ eqToHom hY.symm := by
  have hgs : Function.Surjective (𝓖.p.map g).hom :=
    surjective_map_of_isHomLift gb g hgl hgb
  have hpb : IsPullback (c₀.fst ≫ eqToHom hX.symm) (c₀.snd ≫ eqToHom hY.symm)
      (𝓖.p.map f) (𝓖.p.map g) :=
    (IsPullback.of_isLimit hc₀).of_iso (Iso.refl _) (eqToIso hX.symm) (eqToIso hY.symm)
      (eqToIso hZ.symm) (by simp) (by simp)
      (by rw [IsHomLift.fac' 𝓖.p fb f]; simp) (by rw [IsHomLift.fac' 𝓖.p gb g]; simp)
  exact exists_pullbackCone_with_base 𝓖 hG f g hgs (PullbackCone.mk _ _ hpb.w) hpb.isLimit

/-- A morphism factoring through a cone lies over a morphism factoring through a cone in the base,
as soon as the first cone lies over the second one and the two factorizations are compatible
factorwise. This is the verticality of the morphism induced into an assembled fibre product. -/
private theorem isHomLift_of_pullback_fac
    {F : Type u₂} [Category.{v₂} F] (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    {xb yb zb tb : ArtinianLocalAlgCat.{u, w, w} Λ k} {fb : xb ⟶ zb} {gb : yb ⟶ zb}
    {c₀ : PullbackCone fb gb} (hc₀ : IsLimit c₀)
    {Xc Yc Tc Pc : F} {cfst : Pc ⟶ Xc} {csnd : Pc ⟶ Yc}
    (hX : p.obj Xc = xb) (hY : p.obj Yc = yb) (hT : p.obj Tc = tb)
    (hpt : p.obj Pc = c₀.pt)
    (hfst : p.map cfst = eqToHom hpt ≫ c₀.fst ≫ eqToHom hX.symm)
    (hsnd : p.map csnd = eqToHom hpt ≫ c₀.snd ≫ eqToHom hY.symm)
    {ab : tb ⟶ xb} {bb : tb ⟶ yb} {t₀ : tb ⟶ c₀.pt}
    (ht₀fst : t₀ ≫ c₀.fst = ab) (ht₀snd : t₀ ≫ c₀.snd = bb)
    {ac : Tc ⟶ Xc} {bc : Tc ⟶ Yc} {t : Tc ⟶ Pc}
    (htfst : t ≫ cfst = ac) (htsnd : t ≫ csnd = bc)
    (hab : p.IsHomLift ab ac) (hbb : p.IsHomLift bb bc) :
    p.IsHomLift t₀ t := by
  subst hX hY hT
  simp only [eqToHom_refl, Category.comp_id] at hfst hsnd
  apply IsHomLift.of_fac' p t₀ t rfl hpt
  have leg {x : F} (c : Pc ⟶ x) (a : Tc ⟶ x) (ab : p.obj Tc ⟶ p.obj x) (f₀ : c₀.pt ⟶ p.obj x)
      (hc : p.map c = eqToHom hpt ≫ f₀) (h : t ≫ c = a) (h₀ : t₀ ≫ f₀ = ab)
      (hl : p.IsHomLift ab a) : (p.map t ≫ eqToHom hpt) ≫ f₀ = t₀ ≫ f₀ := by
    rw [Category.assoc, ← hc, ← p.map_comp, h, IsHomLift.fac' p ab a, h₀]
    simp
  have heq : p.map t ≫ eqToHom hpt = t₀ := by
    apply PullbackCone.IsLimit.hom_ext hc₀
    · exact leg _ _ _ _ hfst htfst ht₀fst hab
    · exact leg _ _ _ _ hsnd htsnd ht₀snd hbb
  apply (cancel_mono (eqToHom hpt)).mp
  simpa using heq

/-- Condition (RS) for a product over the base, stated for the structure functor of the product.
`Deformation.piBasedCategory_satisfiesRS` is this result for the product as a based category. -/
private theorem satisfiesRS_structureFunctor
    {ι : Type uι}
    (𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : ∀ i, SatisfiesRS (𝓖 i).p) :
    SatisfiesRS (PiOver.structureFunctor (fun i => (𝓖 i).p)) := by
  classical
  refine ⟨piBasedCategory_isCofiberedInGroupoids 𝓖 (fun i => (hG i).1), ?_⟩
  intro X Y Z f g hg
  have hgb : Function.Surjective g.hbase.hom := hg
  let : HasPullback f.hbase g.hbase :=
    (ArtinianLocalAlgCat.hasPullback_of_surjective f.hbase g.hbase (Or.inr hgb)).2
  obtain ⟨c₀, ⟨hc₀⟩⟩ : ∃ c₀ : PullbackCone f.hbase g.hbase, Nonempty (IsLimit c₀) :=
    ⟨pullback.cone f.hbase g.hbase, ⟨pullback.isLimit f.hbase g.hbase⟩⟩
  have hcomponent (i) :
      ∃ (c : PullbackCone (f.component i) (g.component i))
        (hc : (𝓖 i).p.obj c.pt = c₀.pt),
        Nonempty (IsLimit c) ∧
        (𝓖 i).p.map c.fst = eqToHom hc ≫ c₀.fst ≫ eqToHom (X.hx i).symm ∧
        (𝓖 i).p.map c.snd = eqToHom hc ≫ c₀.snd ≫ eqToHom (Y.hx i).symm :=
    exists_pullbackCone_component (𝓖 i) (hG i) hc₀ hgb (X.hx i) (Y.hx i) (Z.hx i)
      (f.component i) (g.component i) (f.hcomponent i) (g.hcomponent i)
  choose c hpt hc hfst hsnd using hcomponent
  let hci i := Classical.choice (hc i)
  let Q : PiOver (fun i => (𝓖 i).p) := ⟨c₀.pt, fun i => (c i).pt, hpt⟩
  let a : Q ⟶ X := ⟨c₀.fst, fun i => (c i).fst,
    fun i => IsHomLift.of_fac' _ _ _ (hpt i) (X.hx i) (hfst i)⟩
  let b : Q ⟶ Y := ⟨c₀.snd, fun i => (c i).snd,
    fun i => IsHomLift.of_fac' _ _ _ (hpt i) (Y.hx i) (hsnd i)⟩
  have hcond : a ≫ f = b ≫ g := by
    apply PiOver.Hom.ext'
    · exact c₀.condition
    · exact fun i => (c i).condition
  have hlimit : IsLimit (PullbackCone.mk a b hcond) := by
    refine PullbackCone.IsLimit.mk hcond (fun s => ?_) (fun s => ?_) (fun s => ?_)
      (fun s m hm₁ hm₂ => ?_)
    · refine ⟨PullbackCone.IsLimit.lift hc₀ s.fst.hbase s.snd.hbase
          (congrArg PiOver.Hom.hbase s.condition),
        fun i => PullbackCone.IsLimit.lift (hci i) (s.fst.component i) (s.snd.component i)
          (congrArg (fun q => PiOver.Hom.component q i) s.condition),
        fun i => ?_⟩
      exact isHomLift_of_pullback_fac (𝓖 i).p hc₀ (X.hx i) (Y.hx i) (s.pt.hx i) (hpt i)
        (hfst i) (hsnd i)
        (PullbackCone.IsLimit.lift_fst hc₀ _ _ _) (PullbackCone.IsLimit.lift_snd hc₀ _ _ _)
        (PullbackCone.IsLimit.lift_fst (hci i) _ _ _)
        (PullbackCone.IsLimit.lift_snd (hci i) _ _ _)
        (s.fst.hcomponent i) (s.snd.hcomponent i)
    · apply PiOver.Hom.ext'
      · exact PullbackCone.IsLimit.lift_fst hc₀ _ _ _
      · exact fun i => PullbackCone.IsLimit.lift_fst (hci i) _ _ _
    · apply PiOver.Hom.ext'
      · exact PullbackCone.IsLimit.lift_snd hc₀ _ _ _
      · exact fun i => PullbackCone.IsLimit.lift_snd (hci i) _ _ _
    · apply PiOver.Hom.ext'
      · apply PullbackCone.IsLimit.hom_ext hc₀
        · exact (congrArg PiOver.Hom.hbase hm₁).trans
            (PullbackCone.IsLimit.lift_fst hc₀ _ _ _).symm
        · exact (congrArg PiOver.Hom.hbase hm₂).trans
            (PullbackCone.IsLimit.lift_snd hc₀ _ _ _).symm
      · intro i
        apply PullbackCone.IsLimit.hom_ext (hci i)
        · exact (congrArg (fun q => PiOver.Hom.component q i) hm₁).trans
            (PullbackCone.IsLimit.lift_fst (hci i) _ _ _).symm
        · exact (congrArg (fun q => PiOver.Hom.component q i) hm₂).trans
            (PullbackCone.IsLimit.lift_snd (hci i) _ _ _).symm
  refine ⟨PullbackCone.mk a b hcond, ⟨hlimit⟩, ⟨?_⟩⟩
  change IsLimit (PullbackCone.mk c₀.fst c₀.snd ?_)
  exact (IsPullback.of_isLimit hc₀).isLimit

/-- **A product over the base of categories satisfying (RS) satisfies (RS).** A cospan in the
product is a cospan of bases together with one cospan in each factor, and its fibre product is
assembled from the fibre product of the bases — which exists because one leg of the base cospan is
surjective — and the fibre product in each factor over it, supplied by (RS) in that factor. -/
public theorem piBasedCategory_satisfiesRS
    {ι : Type uι}
    (𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : ∀ i, SatisfiesRS (𝓖 i).p) :
    SatisfiesRS (piBasedCategory 𝓖).p :=
  satisfiesRS_structureFunctor 𝓖 hG

/-- **A product over the base of deformation categories is a deformation category.** This is what
makes the smoothness criterion of Stacks 0DYP available at the finite products of deformation
categories appearing in the chain of Stacks 0DZF. -/
public theorem piBasedCategory_isDeformationCategory
    {ι : Type uι}
    (𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hG : ∀ i, IsDeformationCategory (𝓖 i).p) :
    IsDeformationCategory (piBasedCategory 𝓖).p :=
  ⟨piBasedCategory_isPredeformationCategory 𝓖 (fun i => (hG i).predeformation),
    piBasedCategory_satisfiesRS 𝓖 (fun i => (hG i).satisfiesRS)⟩

end

end Deformation
