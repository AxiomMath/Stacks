module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.CategoryTheory.CofilteredSystem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSitePointSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Artinian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-!
# Points of the small étale site and of the small étale topos are geometric points

Let `B` be a big étale site containing a scheme `S`. A point of the small étale site of `S` is a
fibre functor `u : S_étale ⥤ Type*` satisfying the axioms of Stacks 00Y5, and every geometric
point `s` of `S` gives one, namely `AlgebraicGeometry.geometricPointSitePoint`, whose fibre
functor sends an étale `S`-scheme to the set of lifts of `s` to it. This file proves the
converse: *every* point of the small étale site arises this way, and so does every point of
the small étale *topos*, whose inverse image is then the geometric stalk functor — the colimit
over the category of étale neighbourhoods of the geometric point.

The argument has three steps. First the point has a *support*: the opens of `S` whose associated
étale object has nonempty fibre form the neighbourhood filter of a unique point `x` of `S`,
because `S` is sober and the three axioms of a point make that collection of opens a
prime filter. Second, a geometric point `s` above `x` admits a natural map `u ⟶ F_s` from the
given fibre functor to the functor of lifts of `s`, obtained as a section of a cofiltered system
of finite nonempty sets: over an *affine* étale object the lifts of a geometric point are finite,
because an étale algebra over a field is finite. Third, that map is bijective on affine objects —
injectivity because two morphisms agreeing after an unramified separated map agree on a clopen,
and surjectivity by a cardinality count against the reverse natural map — and affine objects are
cofinal, so it is bijective everywhere.

## Main results

* `AlgebraicGeometry.exists_geometricPoint_fiber_iso`: the fibre functor of a point of the small
  étale site is naturally isomorphic to the functor of lifts of a geometric point.
* `AlgebraicGeometry.exists_geometricPoint_sitePoint_iso`: the same conclusion as an isomorphism
  of points of the site.
* `AlgebraicGeometry.exists_geometricPoint_inverseImage_iso`: the inverse image of a point of
  the small étale topos is the geometric stalk functor of a geometric point.

## Implementation notes

The universe of the values of the fibre functor is left free, as `Type (max u w)`, wherever that
costs nothing; the two main results on points of the site force it to be the universe `u` of the
schemes, since a functor isomorphism with `AlgebraicGeometry.geometricPointFiber` requires a
common codomain. For a point of the topos the sheaves take values in `Type (u + 1)`, which is
the universe in which the reconstructed site point of
`PointOfTopos.exists_sitePoint_fiber_eq` lives;
the comparison with `AlgebraicGeometry.geometricPointFiber` is then an equivalence of categories
of elements across two universes, which is what `elementsEquivalenceOfFiberEquivs` allows.

The support of a point is extracted from a functor on `S.Opens` rather than from the point
itself, so that the only input to the sober-space argument is the three nonemptiness properties
of `openFiber` and none of the site structure.

## References

* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t w₁ w₂

namespace AlgebraicGeometry

/-! ### Natural maps out of a cofiltered system of finite fibres -/

/-- A functor to types has a global section as soon as it has one after restriction along an
initial functor. -/
private theorem nonempty_sections_of_initial {C : Type u} [Category.{v} C]
    {D : Type*} [Category* D] (K : C ⥤ D) [K.Initial] (G : D ⥤ Type w)
    (h : (K ⋙ G).sections.Nonempty) : G.sections.Nonempty := by
  obtain ⟨s, hs⟩ := h
  let c : Cone (K ⋙ G) :=
    { pt := PUnit
      π := { app X := ↾fun _ => s X
             naturality X Y f := by ext; exact (hs f).symm } }
  let d : Cone G := Functor.Initial.extendCone.obj c
  refine ⟨fun X => d.π.app X PUnit.unit, ?_⟩
  intro X Y f
  exact ConcreteCategory.congr_hom (d.w f) PUnit.unit

/-- A natural family of maps `F ⟶ G` exists as soon as the objects of `F.Elements` cut out by a
property `P` are cofinal and `G` is finite and nonempty on them.

The family is a global section of the system of values of `G` over the neighbourhoods of `F`,
which exists because that system is cofiltered with finite nonempty values. -/
private theorem exists_natTrans_of_finite_cofinal {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) (G : C ⥤ Type t) [IsCofiltered F.Elements]
    (P : ObjectProperty F.Elements)
    (hrefine : ∀ a, ∃ b : P.FullSubcategory, Nonempty (b.obj ⟶ a))
    (hfinite : ∀ b : P.FullSubcategory, Finite (G.obj b.obj.1))
    (hne : ∀ b : P.FullSubcategory, Nonempty (G.obj b.obj.1)) :
    ∃ c : ∀ X, F.obj X → G.obj X,
      ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), G.map f (c X x) = c Y (F.map f x) := by
  let K := P.ι
  have : K.Initial :=
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful K hrefine
  have : IsCofiltered P.FullSubcategory :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful K hrefine
  let H := Functor.Elements.π F ⋙ G
  have (b : P.FullSubcategory) : Finite ((K ⋙ H).obj b) := hfinite b
  have (b : P.FullSubcategory) : Nonempty ((K ⋙ H).obj b) := hne b
  obtain ⟨s, hs⟩ := nonempty_sections_of_initial K H
    (nonempty_sections_of_finite_cofiltered_system (K ⋙ H))
  refine ⟨fun X x => s (F.elementsMk X x), ?_⟩
  intro X Y f x
  exact hs (Functor.Elements.homMk (x := F.elementsMk X x) (y := F.elementsMk Y (F.map f x)) f rfl)

/-- A natural family of maps between two functors with cofiltered categories of elements is
bijective everywhere as soon as it is bijective on a cofinal class of objects. -/
private theorem bijective_of_bijective_on_cofinal {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) (G : C ⥤ Type t) [IsCofiltered F.Elements] [IsCofiltered G.Elements]
    (P : ObjectProperty C)
    (hF : ∀ a : F.Elements, ∃ b : F.Elements, P b.1 ∧ Nonempty (b ⟶ a))
    (hG : ∀ a : G.Elements, ∃ b : G.Elements, P b.1 ∧ Nonempty (b ⟶ a))
    (α : ∀ X, F.obj X → G.obj X)
    (hnat : ∀ {X Y} (f : X ⟶ Y) (a : F.obj X), G.map f (α X a) = α Y (F.map f a))
    (hα : ∀ X, P X → Function.Bijective (α X)) (X : C) :
    Function.Bijective (α X) := by
  constructor
  · intro a b hab
    let A : F.Elements := F.elementsMk X a
    let B : F.Elements := F.elementsMk X b
    let T := IsCofiltered.min A B
    obtain ⟨T', hT', ⟨r⟩⟩ := hF T
    let f := r ≫ IsCofiltered.minToLeft A B
    let g := r ≫ IsCofiltered.minToRight A B
    let U : G.Elements := G.elementsMk T'.1 (α T'.1 T'.2)
    let V : G.Elements := G.elementsMk X (α X a)
    let f' : U ⟶ V := ⟨f.1, by simpa only [f.2] using (hnat f.1 T'.2)⟩
    let g' : U ⟶ V := ⟨g.1, by
      show G.map g.1 (α T'.1 T'.2) = α X a
      rw [hnat, g.2]
      exact hab.symm⟩
    let W := IsCofiltered.eq f' g'
    let e := IsCofiltered.eqHom f' g'
    obtain ⟨W', hW', ⟨r'⟩⟩ := hG W
    let k := r' ≫ e
    obtain ⟨c, hc⟩ := (hα W'.1 hW').2 W'.2
    have hk : F.map k.1 c = T'.2 := (hα T'.1 hT').1 (by
      rw [← hnat, hc]
      exact k.2)
    have heq : k.1 ≫ f.1 = k.1 ≫ g.1 := by
      show (r'.1 ≫ e.1) ≫ f.1 = (r'.1 ≫ e.1) ≫ g.1
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun h => r'.1 ≫ h.1) (IsCofiltered.eq_condition f' g')
    calc
      a = F.map f.1 T'.2 := f.2.symm
      _ = F.map (k.1 ≫ f.1) c := by rw [Functor.map_comp_apply, hk]
      _ = F.map (k.1 ≫ g.1) c := by rw [heq]
      _ = b := by rw [Functor.map_comp_apply, hk, g.2]
  · intro a
    obtain ⟨T, hT, ⟨f⟩⟩ := hG (G.elementsMk X a)
    obtain ⟨b, hb⟩ := (hα T.1 hT).2 T.2
    exact ⟨F.map f.1 b, by rw [← hnat, hb]; exact f.2⟩

/-! ### Clopen equalizers and finiteness of geometric lifts -/

/-- Two morphisms to a scheme separated and unramified over a base agree on a clopen subscheme
of the source, through which every test morphism equalizing them factors set-theoretically.

The clopen is the preimage of the diagonal, which is an open immersion because the morphism is
unramified and has closed image because it is separated. -/
@[ega "IV 17.4.6"]
private theorem exists_isClosed_opens_equalizer {T X S : Scheme.{u}}
    (f g : T ⟶ X) (h : X ⟶ S) [FormallyUnramified h] [LocallyOfFiniteType h]
    [IsSeparated h] (hfg : f ≫ h = g ≫ h) :
    ∃ U : T.Opens, IsClosed (U : Set T) ∧ U.ι ≫ f = U.ι ≫ g ∧
      ∀ {W : Scheme.{u}} (a : W ⟶ T), a ≫ f = a ≫ g → ∀ w, a w ∈ U := by
  let δ := pullback.diagonal h
  let k := pullback.lift f g hfg
  let U : T.Opens := k ⁻¹ᵁ δ.opensRange
  refine ⟨U, ?_, ?_, ?_⟩
  · exact δ.isClosedEmbedding.isClosed_range.preimage k.continuous
  · have hr : Set.range (U.ι ≫ k) ⊆ Set.range δ := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let l := IsOpenImmersion.lift δ (U.ι ≫ k) hr
    have hl : l ≫ δ = U.ι ≫ k := IsOpenImmersion.lift_fac _ _ _
    have h₁ := congrArg (fun a => a ≫ pullback.fst h h) hl
    have h₂ := congrArg (fun a => a ≫ pullback.snd h h) hl
    simp only [δ, k, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id] at h₁ h₂
    exact h₁.symm.trans h₂
  · intro W a ha w
    have hk : a ≫ k = (a ≫ f) ≫ δ := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, ha, k, δ]
    show k (a w) ∈ Set.range δ
    exact ⟨(a ≫ f) w, (congrArg (fun a => a w) hk).symm⟩

/-- An étale affine scheme over a field has finitely many sections.

Its ring of global functions is an étale algebra over the field, hence a finite module, and a
section is an algebra map out of it. -/
private theorem finite_sections_etale_affine {X : Scheme.{u}} [IsAffine X]
    {Ω : Type u} [Field Ω] (f : X ⟶ Spec (.of Ω)) [Etale f] :
    Finite {g : Spec (.of Ω) ⟶ X // g ≫ f = 𝟙 _} := by
  let e := X.isoSpec
  suffices h : Finite {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _} from
    Finite.of_injective (fun g => (⟨g.1 ≫ e.hom, by simp [g.2]⟩ :
      {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _}))
      fun a b h ↦ Subtype.ext ((cancel_mono e.hom).mp (congrArg Subtype.val h))
  let φ := Spec.homEquiv (e.inv ≫ f)
  have hf : Etale (Spec.map φ) := by
    show Etale (Spec.map (Spec.homEquiv (e.inv ≫ f)))
    simpa using (inferInstance : Etale (e.inv ≫ f))
  let := φ.hom.toAlgebra
  have : Algebra.Etale Ω Γ(X, ⊤) := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hf
  have : Module.Finite Ω Γ(X, ⊤) := Algebra.FormallyUnramified.finite_of_free _ _
  let t (g : {g : Spec (.of Ω) ⟶ Spec Γ(X, ⊤) // g ≫ (e.inv ≫ f) = 𝟙 _}) :
      Γ(X, ⊤) →ₐ[Ω] Ω :=
    { __ := (Spec.homEquiv g.1).hom
      commutes' := by
        intro r
        have hg := congrArg (fun k => Spec.homEquiv k) g.2
        show ((Spec.homEquiv g.1).hom) (φ.hom r) = r
        simpa [φ] using congrArg (fun k => k.hom r) hg }
  exact Finite.of_injective t fun a b h ↦ Subtype.ext <| Spec.homEquiv.injective <| by
    ext r
    exact congrArg (fun k => k r) h

/-- A geometric point of the base has finitely many lifts to an affine scheme étale over it.

Base-changing the étale morphism along the geometric point gives an affine scheme étale over the
algebraically closed field, whose sections are the lifts. -/
private theorem finite_geometric_lifts {X S : Scheme.{u}} [IsAffine X]
    {Ω : Type u} [Field Ω] (f : X ⟶ S) [Etale f] (s : Spec (.of Ω) ⟶ S) :
    Finite {g : Spec (.of Ω) ⟶ X // g ≫ f = s} := by
  let : IsAffineHom s := isAffineHom_of_isArtinianRing s
  let Y := pullback f s
  have : Finite {g : Spec (.of Ω) ⟶ Y // g ≫ pullback.snd f s = 𝟙 _} :=
    finite_sections_etale_affine (pullback.snd f s)
  refine Finite.of_injective (fun g => (⟨pullback.lift g.1 (𝟙 _) (by simpa using g.2),
    pullback.lift_snd _ _ _⟩ : {g : Spec (.of Ω) ⟶ Y // g ≫ pullback.snd f s = 𝟙 _}))
    fun a b h ↦ Subtype.ext ?_
  exact (pullback.lift_fst _ _ _).symm.trans
    ((congrArg (fun g => g.1 ≫ pullback.fst f s) h).trans (pullback.lift_fst _ _ _))

/-! ### Lifting elements of a fibre along coverings and along clopens -/

section Point

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An element of the fibre of a point at `X` comes from the fibre at one member of any family of
morphisms to `X` which is jointly surjective on points.

Such a family generates a covering sieve, and the fibre functor of a point is jointly surjective
on covering sieves. -/
private theorem fiber_exists_of_jointlySurjective
    (p : (SmallEtale.topology B S hS).Point.{max u w}) {X : SmallEtale B S hS} {ι : Type*}
    (Y : ι → SmallEtale B S hS) (f : ∀ i, Y i ⟶ X)
    (hc : ∀ x : X.obj.left.1, ∃ i, x ∈ Set.range (B.inclusion.map (f i).hom.left))
    (a : p.fiber.obj X) : ∃ i b, p.fiber.map (f i) b = a :=
  p.fiber_jointly_surjective_of_ofArrows f
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S hS Y f hc) a

/-- An element of the fibre of a point at `X` lifts either to a clopen of `X` or to its
complement, the two forming a covering of `X`. -/
private theorem fiber_lift_or_lift_compl
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens)
    (hc : IsClosed (U : Set ((SmallEtale.toScheme B S hS).obj X))) (a : p.fiber.obj X) :
    (∃ b, p.fiber.map (SmallEtale.openObjectι B S hS X U) b = a) ∨
      ∃ b : p.fiber.obj (SmallEtale.openObject B S hS X (opensCompl U hc)),
        p.fiber.map (SmallEtale.openObjectι B S hS X (opensCompl U hc)) b = a := by
  classical
  let V : ULift.{u} Bool → ((SmallEtale.toScheme B S hS).obj X).Opens :=
    fun i => if i.down then U else opensCompl U hc
  obtain ⟨i, b, hb⟩ := fiber_exists_of_jointlySurjective B S hS p
    (fun i => SmallEtale.openObject B S hS X (V i))
    (fun i => SmallEtale.openObjectι B S hS X (V i))
    (fun x => by
      have hmem (i : ULift.{u} Bool) (hx : x ∈ V i) :
          x ∈ Set.range (B.inclusion.map
            (SmallEtale.openObjectι B S hS X (V i)).hom.left) := by
        rw [show B.inclusion.map (SmallEtale.openObjectι B S hS X (V i)).hom.left =
          (SmallEtale.toScheme B S hS).map
            (SmallEtale.openObjectι B S hS X (V i)) from rfl,
          SmallEtale.openObjectι_map]
        exact ⟨⟨x, hx⟩, rfl⟩
      by_cases hx : x ∈ U
      · exact ⟨ULift.up true, hmem _ (by simpa [V] using hx)⟩
      · exact ⟨ULift.up false, hmem _ (by simpa [V] using hx)⟩)
    a
  rcases i with ⟨_ | _⟩
  exacts [Or.inr ⟨b, hb⟩, Or.inl ⟨b, hb⟩]

variable (s : GeometricPoint S)

/-- A lift of a geometric point landing in an open subset factors through that open. -/
private theorem geometricPointFiber_lift_of_mem (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens)
    (a : (geometricPointFiber B S hS s).obj X) (ha : a.1 default ∈ U) :
    ∃ b, (geometricPointFiber B S hS s).map (SmallEtale.openObjectι B S hS X U) b = a := by
  have hr : Set.range a.1 ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨a.1 z, by rwa [Subsingleton.elim z default]⟩, rfl⟩
  let b := IsOpenImmersion.lift U.ι a.1 hr
  have hb : b ≫ U.ι = a.1 := IsOpenImmersion.lift_fac _ _ _
  have hι : (SmallEtale.toScheme B S hS).map (SmallEtale.openObjectι B S hS X U) = U.ι :=
    SmallEtale.openObjectι_map B S hS X U
  refine ⟨⟨b, ?_⟩, ?_⟩
  · show b ≫ B.inclusion.map (SmallEtale.openObject B S hS X U).obj.hom = s.hom
    have hcomp : (SmallEtale.toScheme B S hS).map (SmallEtale.openObjectι B S hS X U) ≫
        B.inclusion.map X.obj.hom =
        B.inclusion.map (SmallEtale.openObject B S hS X U).obj.hom :=
      SmallEtale.toScheme_map_comp B S hS _
    rw [← hcomp, hι, ← Category.assoc, hb]
    exact a.2
  · apply Subtype.ext
    show b ≫ (SmallEtale.toScheme B S hS).map (SmallEtale.openObjectι B S hS X U) = a.1
    rwa [hι]

/-- A lift of a geometric point factors through a clopen of an object of the site or through its
complement, according to where its image lies. -/
private theorem geometricPointFiber_lift_or_lift_compl (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens)
    (hc : IsClosed (U : Set ((SmallEtale.toScheme B S hS).obj X)))
    (a : (geometricPointFiber B S hS s).obj X) :
    (∃ b, (geometricPointFiber B S hS s).map
        (SmallEtale.openObjectι B S hS X U) b = a) ∨
      ∃ b : (geometricPointFiber B S hS s).obj
          (SmallEtale.openObject B S hS X (opensCompl U hc)),
        (geometricPointFiber B S hS s).map
          (SmallEtale.openObjectι B S hS X (opensCompl U hc)) b = a := by
  by_cases ha : a.1 default ∈ U
  · exact Or.inl (geometricPointFiber_lift_of_mem B S hS s X U a ha)
  · exact Or.inr (geometricPointFiber_lift_of_mem B S hS s X _ a ha)

/-- A natural map to the lifts of a geometric point is injective at every affine object,
provided elements of the source lift along clopens.

Two elements with the same image are compared on a common refinement; the clopen equalizer of the
two maps out of that refinement either carries the element, in which case the two maps agree on
it, or misses it, in which case the image of the lift escapes the equalizer, which it cannot. -/
private theorem injective_of_natTo_geometricPointFiber
    (F : SmallEtale B S hS ⥤ Type w) [IsCofiltered F.Elements]
    (hlift : ∀ X (U : ((SmallEtale.toScheme B S hS).obj X).Opens)
      (hc : IsClosed (U : Set ((SmallEtale.toScheme B S hS).obj X))) (a : F.obj X),
      (∃ b, F.map (SmallEtale.openObjectι B S hS X U) b = a) ∨
        ∃ b : F.obj (SmallEtale.openObject B S hS X (opensCompl U hc)),
          F.map (SmallEtale.openObjectι B S hS X (opensCompl U hc)) b = a)
    (α : ∀ X, F.obj X → (geometricPointFiber B S hS s).obj X)
    (hnat : ∀ {X Y} (f : X ⟶ Y) (a : F.obj X),
      (geometricPointFiber B S hS s).map f (α X a) = α Y (F.map f a))
    (X : SmallEtale B S hS) (hX : IsAffine ((SmallEtale.toScheme B S hS).obj X)) :
    Function.Injective (α X) := by
  have : IsAffine (B.inclusion.obj X.obj.left) := hX
  intro a b hab
  let A : F.Elements := F.elementsMk X a
  let D : F.Elements := F.elementsMk X b
  let T := IsCofiltered.min A D
  let f := IsCofiltered.minToLeft A D
  let g := IsCofiltered.minToRight A D
  let τ := SmallEtale.toScheme B S hS
  have hfg : τ.map f.1 ≫ B.inclusion.map X.obj.hom =
      τ.map g.1 ≫ B.inclusion.map X.obj.hom := by
    rw [SmallEtale.toScheme_map_comp, SmallEtale.toScheme_map_comp]
  obtain ⟨U, hc, heq, hmem⟩ := exists_isClosed_opens_equalizer
    (τ.map f.1) (τ.map g.1) (B.inclusion.map X.obj.hom) hfg
  have ht : (α T.1 T.2).1 ≫ τ.map f.1 = (α T.1 T.2).1 ≫ τ.map g.1 := by
    have hf := hnat f.1 T.2
    have hg := hnat g.1 T.2
    rw [f.2] at hf
    rw [g.2] at hg
    exact congrArg Subtype.val (hf.trans (hab.trans hg.symm))
  rcases hlift T.1 U hc T.2 with ⟨c, hca⟩ | ⟨c, hca⟩
  · have hf : SmallEtale.openObjectι B S hS T.1 U ≫ f.1 =
        SmallEtale.openObjectι B S hS T.1 U ≫ g.1 := by
      refine (SmallEtale.inclusion B S hS).map_injective
        (Over.OverMorphism.ext (B.inclusion.map_injective ?_))
      show τ.map (SmallEtale.openObjectι B S hS T.1 U ≫ f.1) =
        τ.map (SmallEtale.openObjectι B S hS T.1 U ≫ g.1)
      rw [Functor.map_comp, Functor.map_comp, SmallEtale.openObjectι_map]
      exact heq
    calc
      a = F.map f.1 T.2 := f.2.symm
      _ = F.map (SmallEtale.openObjectι B S hS T.1 U ≫ f.1) c := by
          rw [Functor.map_comp_apply, hca]
      _ = F.map (SmallEtale.openObjectι B S hS T.1 U ≫ g.1) c := by rw [hf]
      _ = b := by rw [Functor.map_comp_apply, hca, g.2]
  · have hn := hnat (SmallEtale.openObjectι B S hS T.1 (opensCompl U hc)) c
    rw [hca] at hn
    have hval : (α _ c).1 ≫
        τ.map (SmallEtale.openObjectι B S hS T.1 (opensCompl U hc)) = (α T.1 T.2).1 :=
      congrArg Subtype.val hn
    have hmemU : ((α T.1 T.2).1) default ∈ U := hmem _ ht default
    have hcompose : ((α T.1 T.2).1) default =
        (opensCompl U hc).ι (((α _ c).1) default) := by
      conv_lhs => rw [← hval]
      rw [SmallEtale.openObjectι_map, Scheme.Hom.comp_apply]
    rw [hcompose] at hmemU
    exact absurd hmemU (((α _ c).1) default).2

/-! ### Comparing the fibre with the lifts of a geometric point above the support -/

/-- The structure morphism of an object of the small étale site lands in its image open. -/
private theorem range_subset_range_imageOpen_ι (X : SmallEtale B S hS) :
    Set.range (B.inclusion.map X.obj.hom).base ⊆
      Set.range (smallEtaleImageOpen B S hS X).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨B.inclusion.map X.obj.hom z, ⟨z, rfl⟩⟩, rfl⟩

/-- The structure morphism of an object of the small étale site, viewed as a morphism onto its
image open. -/
private def imageOpenLift (X : SmallEtale B S hS) :
    B.inclusion.obj X.obj.left ⟶ (smallEtaleImageOpen B S hS X).toScheme :=
  IsOpenImmersion.lift (smallEtaleImageOpen B S hS X).ι (B.inclusion.map X.obj.hom)
    (range_subset_range_imageOpen_ι B S hS X)

/-- Composing the lift onto the image open with the inclusion of that open recovers the
structure morphism. -/
private theorem imageOpenLift_ι_fac (X : SmallEtale B S hS) :
    imageOpenLift B S hS X ≫ (smallEtaleImageOpen B S hS X).ι =
      B.inclusion.map X.obj.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- An object of the small étale site factors through its image open in `S`. -/
private def etaleImageFactor (X : SmallEtale B S hS) :
    X ⟶ (opensToBoundedEtale B S hS).obj (smallEtaleImageOpen B S hS X) := by
  refine ⟨Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj X.obj.left ⟶
        B.inclusion.obj ((opensToBoundedEtale B S hS).obj
          (smallEtaleImageOpen B S hS X)).obj.left from imageOpenLift B S hS X)) ?_⟩
  apply B.inclusion.map_injective
  rw [Functor.map_comp, B.inclusion.map_preimage]
  exact imageOpenLift_ι_fac B S hS X

/-- The factorisation of an object through its image open is the lift onto that open. -/
private theorem etaleImageFactor_map (X : SmallEtale B S hS) :
    (SmallEtale.toScheme B S hS).map (etaleImageFactor B S hS X) =
      imageOpenLift B S hS X :=
  B.inclusion.map_preimage _

/-- If the fibre of a point at an object of the site is nonempty then the support of the point
lies in the image of that object. -/
private theorem mem_imageOpen_of_fiber_nonempty
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (X : SmallEtale B S hS) (ha : Nonempty (p.fiber.obj X)) :
    x ∈ (smallEtaleImageOpen B S hS X : Set S) :=
  (hx (smallEtaleImageOpen B S hS X)).2 (ha.map (p.fiber.map (etaleImageFactor B S hS X)))

/-- Conversely, if the support of a point lies in the image of an object of the site then the
fibre at that object is nonempty: the object covers its image open, so the fibre there, which is
nonempty because the image open is a neighbourhood of the support, is hit. -/
private theorem fiber_nonempty_of_mem_imageOpen
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (X : SmallEtale B S hS) (hxX : x ∈ (smallEtaleImageOpen B S hS X : Set S)) :
    Nonempty (p.fiber.obj X) := by
  classical
  obtain ⟨-, b, -⟩ := fiber_exists_of_jointlySurjective B S hS p
    (fun _ : PUnit.{u + 1} => X) (fun _ => etaleImageFactor B S hS X)
    (fun y => by
      refine ⟨PUnit.unit, ?_⟩
      obtain ⟨z, hz⟩ := (show (y.1 : S) ∈ Set.range (B.inclusion.map X.obj.hom) from y.2)
      refine ⟨z, ?_⟩
      rw [show B.inclusion.map (etaleImageFactor B S hS X).hom.left =
        (SmallEtale.toScheme B S hS).map (etaleImageFactor B S hS X) from rfl,
        etaleImageFactor_map]
      apply Subtype.ext
      calc
        (smallEtaleImageOpen B S hS X).ι ((imageOpenLift B S hS X) z)
            = B.inclusion.map X.obj.hom z :=
          congrArg (fun k => k z) (imageOpenLift_ι_fac B S hS X)
        _ = y.1 := hz)
    (Classical.choice ((hx (smallEtaleImageOpen B S hS X)).mp hxX))
  exact ⟨b⟩

/-- A geometric point has finitely many lifts to an affine object of the small étale site. -/
private theorem finite_geometricPointFiber_obj (X : SmallEtale B S hS)
    (hX : IsAffine ((SmallEtale.toScheme B S hS).obj X)) :
    Finite ((geometricPointFiber B S hS s).obj X) := by
  have : IsAffine (B.inclusion.obj X.obj.left) := hX
  exact finite_geometric_lifts (B.inclusion.map X.obj.hom) s.hom

/-- A natural map from the fibre of a point to the lifts of a geometric point above its support.

Over an affine object the lifts are finite, and nonempty because the support lies in the image of
the object and the residue field of the geometric point is separably closed; affine objects are
cofinal, so a natural map exists. -/
private theorem exists_natTo_geometricPointFiber
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (s : GeometricPoint S) (hs : s.hom default = x) :
    ∃ c : ∀ X, p.fiber.obj X → (geometricPointFiber B S hS s).obj X,
      ∀ {X Y} (f : X ⟶ Y) (a : p.fiber.obj X),
        (geometricPointFiber B S hS s).map f (c X a) = c Y (p.fiber.map f a) :=
  exists_natTrans_of_finite_cofinal p.fiber (geometricPointFiber B S hS s)
    (fun a => IsAffine ((SmallEtale.toScheme B S hS).obj a.1))
    (fun a => by
      obtain ⟨b, hb, hba⟩ := exists_isAffine_refinement_fiber B S hS p a
      exact ⟨⟨b, hb⟩, hba⟩)
    (fun b => finite_geometricPointFiber_obj B S hS s b.obj.1 b.property)
    (fun b => by
      obtain ⟨y, hy⟩ := mem_imageOpen_of_fiber_nonempty B S hS p x hx b.obj.1 ⟨b.obj.2⟩
      obtain ⟨g, hg, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
        (B.inclusion.map b.obj.1.obj.hom) s.hom y (hy.trans hs.symm)
      exact ⟨⟨g, hg⟩⟩)

/-- Every étale neighbourhood of a geometric point above the support of a point of the site has
nonempty fibre for that point. -/
private theorem fiber_nonempty_of_geometricPointFiber_elements
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (s : GeometricPoint S) (hsx : s.hom default = x)
    (a : (geometricPointFiber B S hS s).Elements) : Nonempty (p.fiber.obj a.1) := by
  apply fiber_nonempty_of_mem_imageOpen B S hS p x hx a.1
  show x ∈ Set.range (B.inclusion.map a.1.obj.hom).base
  refine ⟨a.2.1 default, ?_⟩
  have h := congrArg (fun f => f default) a.2.2
  change (a.2.1 ≫ B.inclusion.map a.1.obj.hom) default = s.hom default at h
  rw [Scheme.Hom.comp_apply] at h
  exact h.trans hsx

/-- The fibre functor of a point of the small étale site is pointwise equivalent, naturally, to
the functor of lifts of a geometric point above its support. -/
private theorem exists_fiber_equiv_geometricPointFiber
    (p : (SmallEtale.topology B S hS).Point.{max u w}) :
    ∃ s : GeometricPoint S,
      ∃ e : ∀ X, p.fiber.obj X ≃ (geometricPointFiber B S hS s).obj X,
        ∀ {X Y} (f : X ⟶ Y) (a : p.fiber.obj X),
          (geometricPointFiber B S hS s).map f (e X a) = e Y (p.fiber.map f a) := by
  obtain ⟨x, hx⟩ := sitePoint_has_supportPoint B S hS p
  let s := GeometricPoint.ofPoint S x
  have hs : s.hom default = x := GeometricPoint.ofPoint_liesOver S x
  obtain ⟨α, hαnat⟩ := exists_natTo_geometricPointFiber B S hS p x hx s hs
  let G := geometricPointFiber B S hS s
  have hinj (X : SmallEtale B S hS)
      (hX : IsAffine ((SmallEtale.toScheme B S hS).obj X)) : Function.Injective (α X) :=
    injective_of_natTo_geometricPointFiber B S hS s p.fiber
      (fiber_lift_or_lift_compl B S hS p) α hαnat X hX
  obtain ⟨c, hc⟩ := exists_natTrans_of_finite_cofinal G p.fiber
    (fun a => IsAffine ((SmallEtale.toScheme B S hS).obj a.1))
    (fun a => by
      obtain ⟨b, hb, hba⟩ := exists_isAffine_refinement_geometricPointFiber B S hS s a
      exact ⟨⟨b, hb⟩, hba⟩)
    (fun b => by
      have := finite_geometricPointFiber_obj B S hS s b.obj.1 b.property
      exact Finite.of_injective (α b.obj.1) (hinj b.obj.1 b.property))
    (fun b => fiber_nonempty_of_geometricPointFiber_elements B S hS p x hx s hs b.obj)
  have hbij (X : SmallEtale B S hS)
      (hX : IsAffine ((SmallEtale.toScheme B S hS).obj X)) : Function.Bijective (α X) := by
    have := finite_geometricPointFiber_obj B S hS s X hX
    have hi := injective_of_natTo_geometricPointFiber B S hS s G
      (geometricPointFiber_lift_or_lift_compl B S hS s) (fun X z => α X (c X z))
      (fun f z => by rw [hαnat, hc]) X hX
    refine ⟨hinj X hX, fun y => ?_⟩
    obtain ⟨z, hz⟩ := Finite.surjective_of_injective hi y
    exact ⟨c X z, hz⟩
  have hb := bijective_of_bijective_on_cofinal p.fiber G
    (fun X => IsAffine ((SmallEtale.toScheme B S hS).obj X))
    (exists_isAffine_refinement_fiber B S hS p)
    (exists_isAffine_refinement_geometricPointFiber B S hS s) α hαnat hbij
  exact ⟨s, fun X => Equiv.ofBijective (α X) (hb X), hαnat⟩

/-- **Stacks 04HU, part (1).** Every point of the small étale site of `S` is given by a geometric
point of `S`: its fibre functor is naturally isomorphic to the functor of lifts of that geometric
point, which is the fibre functor of
`AlgebraicGeometry.geometricPointSitePoint`. -/
@[stacks 04HU "part (1)", sga "4 VIII 7.9" "essential surjectivity"]
public theorem exists_geometricPoint_fiber_iso
    (p : (SmallEtale.topology B S hS).Point.{u}) :
    ∃ s : GeometricPoint S, Nonempty (p.fiber ≅ geometricPointFiber B S hS s) := by
  obtain ⟨s, e, he⟩ := exists_fiber_equiv_geometricPointFiber B S hS p
  refine ⟨s, ⟨NatIso.ofComponents (fun X => (e X).toIso) fun f => ?_⟩⟩
  ext a
  exact (he f a).symm

/-- Every point of the small étale site of `S` is isomorphic, as a point of the site, to the
point attached to a geometric point of `S`.

This is `AlgebraicGeometry.exists_geometricPoint_fiber_iso` repackaged: a morphism of points of a
site is exactly a natural transformation of fibre functors, so the natural isomorphism of fibre
functors is an isomorphism of points. -/
public theorem exists_geometricPoint_sitePoint_iso
    (p : (SmallEtale.topology B S hS).Point.{u}) :
    ∃ s : GeometricPoint S, Nonempty (p ≅ geometricPointSitePoint B S hS s) := by
  obtain ⟨s, ⟨e⟩⟩ := exists_geometricPoint_fiber_iso B S hS p
  exact ⟨s, ⟨⟨⟨e.inv⟩, ⟨e.hom⟩, GrothendieckTopology.Point.hom_ext e.hom_inv_id,
    GrothendieckTopology.Point.hom_ext e.inv_hom_id⟩⟩⟩

/-! ### Points of the small étale topos -/

/-- Fibre functors that are pointwise equivalent, naturally, have equivalent categories of
elements. -/
private def elementsEquivalenceOfFiberEquivs {C : Type u} [Category.{v} C]
    {F : C ⥤ Type w₁} {G : C ⥤ Type w₂}
    (e : ∀ X, F.obj X ≃ G.obj X)
    (he : ∀ {X Y} (f : X ⟶ Y) (a : F.obj X), G.map f (e X a) = e Y (F.map f a)) :
    F.Elements ≌ G.Elements where
  functor :=
    { obj a := G.elementsMk a.1 (e a.1 a.2)
      map {a b} f := ⟨f.1, (he f.1 a.2).trans (congrArg (e b.1) f.2)⟩
      map_id a := rfl
      map_comp f g := rfl }
  inverse :=
    { obj a := F.elementsMk a.1 ((e a.1).symm a.2)
      map {a b} f := ⟨f.1, by
        apply (e b.1).injective
        rw [← he]
        simp⟩
      map_id a := rfl
      map_comp f g := rfl }
  unitIso := NatIso.ofComponents (fun a =>
    Functor.Elements.isoMk (Iso.refl _) (by
      change F.map (𝟙 a.1) a.2 = (e a.1).symm (e a.1 a.2)
      simp)) (by
      intro a b f
      apply Functor.Elements.hom_ext
      change f.1 ≫ 𝟙 _ = 𝟙 _ ≫ f.1
      simp)
  counitIso := NatIso.ofComponents (fun a =>
    Functor.Elements.isoMk (Iso.refl _) (by
      change G.map (𝟙 a.1) (e a.1 ((e a.1).symm a.2)) = a.2
      simp)) (by
      intro a b f
      apply Functor.Elements.hom_ext
      change f.1 ≫ 𝟙 _ = 𝟙 _ ≫ f.1
      simp)
  functor_unitIso_comp a := by
    apply Functor.Elements.hom_ext
    change (𝟙 a.1) ≫ 𝟙 a.1 = 𝟙 a.1
    simp

/-- Equivalent fibre functors have naturally isomorphic presheaf stalk functors. The comparison
is induced by the equivalence of the categories of elements. -/
private noncomputable def presheafFiberIsoOfFiberIso
    {C : Type u} [Category.{v} C] {F : C ⥤ Type w₁} {G : C ⥤ Type w₂}
    (e : ∀ X, F.obj X ≃ G.obj X)
    (he : ∀ {X Y} (f : X ⟶ Y) (a : F.obj X), G.map f (e X a) = e Y (F.map f a))
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)]
    [HasColimitsOfShape G.Elementsᵒᵖ (Type w)] :
    (Functor.whiskeringLeft F.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
        (Functor.Elements.π F).op ⋙ colim ≅
      (Functor.whiskeringLeft G.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
        (Functor.Elements.π G).op ⋙ colim := by
  let E := elementsEquivalenceOfFiberEquivs e he
  let K := E.functor.op
  have hK : K ⋙ (Functor.Elements.π G).op = (Functor.Elements.π F).op := rfl
  have : K.Final := Functor.final_equivalence_comp (𝟭 _) K
  let H := (Functor.whiskeringLeft G.Elementsᵒᵖ Cᵒᵖ (Type w)).obj (Functor.Elements.π G).op
  let HK := (Functor.whiskeringLeft F.Elementsᵒᵖ G.Elementsᵒᵖ (Type w)).obj K
  have hH : H ⋙ HK =
      (Functor.whiskeringLeft F.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
        (K ⋙ (Functor.Elements.π G).op) := rfl
  have hcomp := congrArg
    (fun q : F.Elementsᵒᵖ ⥤ Cᵒᵖ =>
      (Functor.whiskeringLeft F.Elementsᵒᵖ Cᵒᵖ (Type w)).obj q ⋙ colim) hK
  have hsrc : (H ⋙ HK) ⋙ colim =
      (Functor.whiskeringLeft F.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
        (Functor.Elements.π F).op ⋙ colim := by
    rw [hH, hcomp]
  exact (eqToIso hsrc).symm ≪≫ Functor.associator H HK colim ≪≫
    Functor.isoWhiskerLeft H (Functor.Final.colimIso K)

/-- The same comparison after restricting along `sheafToPresheaf`. -/
private noncomputable def sheafFiberIsoOfFiberIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : C ⥤ Type w₁} {G : C ⥤ Type w₂}
    (e : ∀ X, F.obj X ≃ G.obj X)
    (he : ∀ {X Y} (f : X ⟶ Y) (a : F.obj X), G.map f (e X a) = e Y (F.map f a))
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)]
    [HasColimitsOfShape G.Elementsᵒᵖ (Type w)] :
    sheafToPresheaf J (Type w) ⋙
        ((Functor.whiskeringLeft F.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
          (Functor.Elements.π F).op ⋙ colim) ≅
      sheafToPresheaf J (Type w) ⋙
        ((Functor.whiskeringLeft G.Elementsᵒᵖ Cᵒᵖ (Type w)).obj
          (Functor.Elements.π G).op ⋙ colim) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (Type w)) (presheafFiberIsoOfFiberIso e he)

/-- **Stacks 04HU, part (2).** Every point of the small étale topos of `S` has the geometric
stalk functor of a geometric point of `S` as its inverse image: the stalk of a sheaf `F` at the
point is the colimit of `F` over the category of étale neighbourhoods of that geometric point.

The point of the topos is first reconstructed as a point of the site
(`PointOfTopos.exists_sitePoint_fiber_eq`, Stacks 00YA (2)); that point of the site is then a
geometric point by `AlgebraicGeometry.exists_geometricPoint_fiber_iso`, part (1), and the
canonical comparison identifies the two inverse images
(`PointOfTopos.isIso_sheafFiberComparison`). -/
@[stacks 04HU "part (2)", sga "4 VIII 7.9" "essential surjectivity"]
public theorem exists_geometricPoint_inverseImage_iso
    (p : PointOfTopos.{u + 1} (SmallEtale.topology B S hS)) :
    ∃ s : GeometricPoint S,
      Nonempty (p.inverseImage ≅
        sheafToPresheaf (SmallEtale.topology B S hS) (Type (u + 1)) ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
          colim) := by
  obtain ⟨Φ, hΦ⟩ := p.exists_sitePoint_fiber_eq
  obtain ⟨s, e, he⟩ := exists_fiber_equiv_geometricPointFiber.{u, u + 1} B S hS Φ
  let i := eqToIso hΦ
  have : IsIso (Φ.sheafFiberComparison p.inverseImage i.hom) :=
    p.isIso_sheafFiberComparison Φ i
  exact ⟨s, ⟨(asIso (Φ.sheafFiberComparison p.inverseImage i.hom)).symm ≪≫
    sheafFiberIsoOfFiberIso.{u + 1, u, u + 1, u + 1, u} e he⟩⟩

end Point

end AlgebraicGeometry

end
