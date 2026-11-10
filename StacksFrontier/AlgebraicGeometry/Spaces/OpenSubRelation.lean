module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedAffineLine

/-!
# Open subrelations of an étale equivalence relation

Let `s, t : R ⟶ U` be an étale equivalence relation on an object `U` of the big fppf site, let
`r` be a section of both projections, and let `G` be an open subset of `U`. The points of `R`
in the image of `r`, together with the points both of whose projections lie in `G`, form an
open subset of `R`. The open subscheme it defines is again an étale equivalence relation on `U`:
on `G` it relates what `R` relates, and away from `G` it is the trivial relation.

Two morphisms into `U` are related by the open subscheme exactly when they are related by `R`
and, near every point of their source, either both land in `G` or they agree on a neighbourhood
of that point. Agreeing on a neighbourhood is the pointwise form of factoring through the
identity section, whose image is open because a section of an étale morphism is an open
immersion. Written this way the relation is visibly an equivalence relation.

## Main definitions

* `AlgebraicGeometry.Space.OpenSubRelation.opens`: the open subset of `R`.

## Main results

* `AlgebraicGeometry.Space.OpenSubRelation.isEtaleEquivalenceRelation`: the open subscheme of
  `R` on that set is an étale equivalence relation on `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space.OpenSubRelation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- An étale equivalence relation has a section of both of its projections. -/
theorem exists_identitySection [IsEtaleEquivalenceRelation (Space.relation B S hS s t)] :
    ∃ r : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj R,
      r ≫ (Over.post B.inclusion).map t = 𝟙 _ ∧ r ≫ (Over.post B.inclusion).map s = 𝟙 _ := by
  have hpre := isPreEquivalenceRelation_of_isEtaleEquivalenceRelation (Space.relation B S hS s t)
  obtain ⟨r, h₁, h₂⟩ := (hpre _).refl (𝟙 ((Over.post B.inclusion).obj U))
  rw [TwistedAffineLine.relation_target_eq] at h₁
  rw [TwistedAffineLine.relation_source_eq] at h₂
  exact ⟨r, h₁, h₂⟩

variable {B S hS s t}
/-- The source projection of an étale equivalence relation is étale. -/
private theorem etale_map_source_left
    [h : IsEtaleEquivalenceRelation (Space.relation B S hS s t)] :
    Etale ((Over.post B.inclusion).map s).left := by
  have := h.etale_source
  rwa [TwistedAffineLine.relation_source_eq] at this

/-- The target projection of an étale equivalence relation is étale. -/
private theorem etale_map_target_left
    [h : IsEtaleEquivalenceRelation (Space.relation B S hS s t)] :
    Etale ((Over.post B.inclusion).map t).left := by
  have := h.etale_target
  rwa [TwistedAffineLine.relation_target_eq] at this

variable [hrel : IsEtaleEquivalenceRelation (Space.relation B S hS s t)]
variable (r : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj R)
    (hrt : r ≫ (Over.post B.inclusion).map t = 𝟙 _)
    (hrs : r ≫ (Over.post B.inclusion).map s = 𝟙 _)

/-- A section of a projection is a section on the underlying schemes. -/
private theorem identitySection_left_comp (f : R ⟶ U)
    (h : r ≫ (Over.post B.inclusion).map f = 𝟙 _) :
    r.left ≫ ((Over.post B.inclusion).map f).left = 𝟙 _ :=
  congrArg CommaMorphism.left h

include hrel hrs in
/-- The identity section is an open immersion. -/
theorem isOpenImmersion_identitySection : _root_.AlgebraicGeometry.IsOpenImmersion r.left := by
  have := etale_map_source_left (s := s) (t := t)
  exact isOpenImmersion_of_section_of_etale ((Over.post B.inclusion).map s).left r.left
    (congrArg CommaMorphism.left hrs)

/-- Two morphisms into `U` *agree near* a point of their source when they agree on an open
neighbourhood of it. -/
def AgreeNear {T : Over (B.inclusion.obj (B.obj hS))}
    (a b : T ⟶ (Over.post B.inclusion).obj U) (p : T.left) : Prop :=
  ∃ N : T.left.Opens, p ∈ N ∧ N.ι ≫ a.left = N.ι ≫ b.left

omit hrel in
/-- Every morphism into `U` agrees near any point with itself. -/
theorem AgreeNear.refl {T : Over (B.inclusion.obj (B.obj hS))}
    (a : T ⟶ (Over.post B.inclusion).obj U) (p : T.left) : AgreeNear a a p :=
  ⟨⊤, trivial, rfl⟩

omit hrel in
/-- Agreeing near a point is symmetric. -/
theorem AgreeNear.symm {T : Over (B.inclusion.obj (B.obj hS))}
    {a b : T ⟶ (Over.post B.inclusion).obj U} {p : T.left} (h : AgreeNear a b p) :
    AgreeNear b a p := by
  obtain ⟨N, hp, hN⟩ := h
  exact ⟨N, hp, hN.symm⟩

omit hrel in
/-- Agreeing near a point is transitive. -/
theorem AgreeNear.trans {T : Over (B.inclusion.obj (B.obj hS))}
    {a b c : T ⟶ (Over.post B.inclusion).obj U} {p : T.left} (h₁ : AgreeNear a b p)
    (h₂ : AgreeNear b c p) : AgreeNear a c p := by
  obtain ⟨N₁, hp₁, hN₁⟩ := h₁
  obtain ⟨N₂, hp₂, hN₂⟩ := h₂
  refine ⟨N₁ ⊓ N₂, ⟨hp₁, hp₂⟩, ?_⟩
  have e₁ := congrArg (T.left.homOfLE (inf_le_left : N₁ ⊓ N₂ ≤ N₁) ≫ ·) hN₁
  have e₂ := congrArg (T.left.homOfLE (inf_le_right : N₁ ⊓ N₂ ≤ N₂) ≫ ·) hN₂
  simp only [← Category.assoc, Scheme.homOfLE_ι] at e₁ e₂
  exact e₁.trans e₂

omit hrel in
/-- Two morphisms that agree near a point take the same value at that point. -/
theorem AgreeNear.apply_eq {T : Over (B.inclusion.obj (B.obj hS))}
    {a b : T ⟶ (Over.post B.inclusion).obj U} {p : T.left} (h : AgreeNear a b p) :
    a.left p = b.left p := by
  obtain ⟨N, hp, hN⟩ := h
  have := congrArg (fun f ↦ f ⟨p, hp⟩) hN
  change a.left (N.ι ⟨p, hp⟩) = b.left (N.ι ⟨p, hp⟩) at this
  exact this

include hrt hrs in
/-- **A point of `R` lies in the image of the identity section exactly when its two projections
agree near it**, read on a morphism into `R`. -/
theorem mem_range_identitySection_iff {T : Over (B.inclusion.obj (B.obj hS))}
    (g : T ⟶ (Over.post B.inclusion).obj R) (p : T.left) :
    g.left p ∈ Set.range r.left ↔
      AgreeNear (g ≫ (Over.post B.inclusion).map t) (g ≫ (Over.post B.inclusion).map s) p := by
  have := isOpenImmersion_identitySection (t := t) r hrs
  constructor
  · intro hp
    let N : T.left.Opens := g.left ⁻¹ᵁ r.left.opensRange
    have hrange : Set.range (N.ι ≫ g.left) ⊆ Set.range r.left := by
      rintro _ ⟨q, rfl⟩
      exact q.2
    set l := IsOpenImmersion.lift r.left (N.ι ≫ g.left) hrange with hl
    have hfac : l ≫ r.left = N.ι ≫ g.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨N, hp, ?_⟩
    change N.ι ≫ g.left ≫ ((Over.post B.inclusion).map t).left =
      N.ι ≫ g.left ≫ ((Over.post B.inclusion).map s).left
    rw [← Category.assoc, ← Category.assoc, ← hfac, Category.assoc, Category.assoc,
      identitySection_left_comp r t hrt, identitySection_left_comp r s hrs]
  · rintro ⟨N, hp, hN⟩
    let TN : Over (B.inclusion.obj (B.obj hS)) := Over.mk (N.ι ≫ T.hom)
    let iN : TN ⟶ T := Over.homMk N.ι rfl
    have hts : iN ≫ g ≫ (Over.post B.inclusion).map t =
        iN ≫ g ≫ (Over.post B.inclusion).map s := by
      ext1
      exact hN
    have hmono := mono_of_isEtaleEquivalenceRelation (Space.relation B S hS s t)
    have heq : iN ≫ g = (iN ≫ g ≫ (Over.post B.inclusion).map t) ≫ r := by
      refine (cancel_mono (Space.relation B S hS s t)).1 (prod.hom_ext ?_ ?_)
      · simp only [Space.relation, Category.assoc, prod.lift_fst, hrt, Category.comp_id]
      · simp only [Space.relation, Category.assoc, prod.lift_snd, hrs, Category.comp_id, hts]
    have h := congrArg (fun f : TN ⟶ (Over.post B.inclusion).obj R ↦
      f.left (show TN.left from ⟨p, hp⟩)) heq
    simp only [Over.comp_left] at h
    exact ⟨_, h.symm⟩

variable (s t) in
/-- The open subset of `R` made of the image of the identity section and of the points both of
whose projections lie in `G`. -/
def opens (G : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    ((BigFppfOver.toScheme B S hS).obj R).Opens :=
  ⟨Set.range r.left ∪ ((BigFppfOver.toScheme B S hS).map t ⁻¹' G ∩
      (BigFppfOver.toScheme B S hS).map s ⁻¹' G), by
    have := isOpenImmersion_identitySection (t := t) r hrs
    exact r.left.isOpenEmbedding.isOpen_range.union
      ((G.isOpen.preimage ((BigFppfOver.toScheme B S hS).map t).continuous).inter
        (G.isOpen.preimage ((BigFppfOver.toScheme B S hS).map s).continuous))⟩

variable (s t) in
/-- A point of `R` lies in `AlgebraicGeometry.Space.OpenSubRelation.opens` exactly when it is in
the image of the identity section or both of its projections lie in `G`. -/
theorem mem_opens_iff (G : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ε : (BigFppfOver.toScheme B S hS).obj R) :
    ε ∈ opens s t r hrs G ↔ ε ∈ Set.range r.left ∨
      ((BigFppfOver.toScheme B S hS).map t ε ∈ G ∧ (BigFppfOver.toScheme B S hS).map s ε ∈ G) :=
  Iff.rfl

variable (s t) in
/-- The open subscheme of `R` on `AlgebraicGeometry.Space.OpenSubRelation.opens`, as an object
of the site. -/
abbrev subObject (G : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  opensObject B S hS R (opens s t r hrs G)

variable (s t) in
/-- The inclusion of the open subrelation. -/
abbrev subι (G : ((BigFppfOver.toScheme B S hS).obj U).Opens) : subObject s t r hrs G ⟶ R :=
  opensObjectι B S hS R (opens s t r hrs G)

include hrt in
/-- **Two morphisms into `U` are related by the open subrelation** exactly when they are related
by `R` and, near every point of the source, they both land in `G` or agree. -/
theorem rel_iff (G : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    {T : Over (B.inclusion.obj (B.obj hS))} (a b : T ⟶ (Over.post B.inclusion).obj U) :
    (Space.relation B S hS (subι s t r hrs G ≫ s) (subι s t r hrs G ≫ t)).Rel a b ↔
      (Space.relation B S hS s t).Rel a b ∧
        ∀ p : T.left, (a.left p ∈ G ∧ b.left p ∈ G) ∨ AgreeNear a b p := by
  constructor
  · rintro ⟨g', hg't, hg's⟩
    rw [TwistedAffineLine.relation_target_eq] at hg't
    rw [TwistedAffineLine.relation_source_eq] at hg's
    set g := g' ≫ (Over.post B.inclusion).map (subι s t r hrs G) with hg
    have h1 : g ≫ (Over.post B.inclusion).map t = a := by
      rw [hg, Category.assoc, ← Functor.map_comp]; exact hg't
    have h2 : g ≫ (Over.post B.inclusion).map s = b := by
      rw [hg, Category.assoc, ← Functor.map_comp]; exact hg's
    refine ⟨⟨g, by rw [TwistedAffineLine.relation_target_eq]; exact h1,
      by rw [TwistedAffineLine.relation_source_eq]; exact h2⟩, fun p ↦ ?_⟩
    have hmem : g.left p ∈ opens s t r hrs G := (g'.left p).2
    rw [← h1, ← h2]
    rcases (mem_opens_iff s t r hrs G _).1 hmem with h | ⟨ht, hs⟩
    exacts [.inr ((mem_range_identitySection_iff r hrt hrs g p).1 h), .inl ⟨ht, hs⟩]
  · rintro ⟨⟨g, hgt, hgs⟩, hp⟩
    rw [TwistedAffineLine.relation_target_eq] at hgt
    rw [TwistedAffineLine.relation_source_eq] at hgs
    have hmem : ∀ p, g.left p ∈ opens s t r hrs G := by
      intro p
      rw [← hgt, ← hgs] at hp
      rcases hp p with h | h
      exacts [.inr h, .inl ((mem_range_identitySection_iff r hrt hrs g p).2 h)]
    have hrange : Set.range g.left ⊆ Set.range (opens s t r hrs G).ι := by
      rintro _ ⟨p, rfl⟩
      exact ⟨⟨_, hmem p⟩, rfl⟩
    set l := IsOpenImmersion.lift (opens s t r hrs G).ι g.left hrange with hl
    have hfac : l ≫ (opens s t r hrs G).ι = g.left := IsOpenImmersion.lift_fac _ _ _
    let g' : T ⟶ (Over.post B.inclusion).obj (subObject s t r hrs G) :=
      Over.homMk l (by
        change l ≫ (opens s t r hrs G).ι ≫ B.inclusion.map R.hom = T.hom
        rw [← Category.assoc, hfac]
        exact Over.w g)
    have hg' : g' ≫ (Over.post B.inclusion).map (subι s t r hrs G) = g := by
      ext1
      exact hfac
    refine ⟨g', ?_, ?_⟩
    · rw [TwistedAffineLine.relation_target_eq, Functor.map_comp, ← Category.assoc, hg', hgt]
    · rw [TwistedAffineLine.relation_source_eq, Functor.map_comp, ← Category.assoc, hg', hgs]

include hrt in
/-- **Stacks 02WS for an open subrelation.** The open subscheme of `R` made of the image of the
identity section and of the points both of whose projections lie in `G` is an étale
equivalence relation on `U`. -/
theorem isEtaleEquivalenceRelation (G : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    IsEtaleEquivalenceRelation
      (Space.relation B S hS (subι s t r hrs G ≫ s) (subι s t r hrs G ≫ t)) := by
  have hmono := mono_of_isEtaleEquivalenceRelation (Space.relation B S hS s t)
  have hpre := isPreEquivalenceRelation_of_isEtaleEquivalenceRelation (Space.relation B S hS s t)
  have hmono' : Mono
      (Space.relation B S hS (subι s t r hrs G ≫ s) (subι s t r hrs G ≫ t)) := by
    constructor
    intro Z f g hfg
    have ht := congrArg (· ≫ prod.fst) hfg
    have hs := congrArg (· ≫ prod.snd) hfg
    simp only [Category.assoc, Space.relation, prod.lift_fst, prod.lift_snd,
      Functor.map_comp] at ht hs
    have h : f ≫ (Over.post B.inclusion).map (subι s t r hrs G) =
        g ≫ (Over.post B.inclusion).map (subι s t r hrs G) := by
      refine (cancel_mono (Space.relation B S hS s t)).1 (prod.hom_ext ?_ ?_)
      · simpa only [Space.relation, Category.assoc, prod.lift_fst] using ht
      · simpa only [Space.relation, Category.assoc, prod.lift_snd] using hs
    ext1
    exact (cancel_mono (opens s t r hrs G).ι).1 (congrArg CommaMorphism.left h)
  have hpre' : Stacks.Groupoids.IsPreEquivalenceRelation
      (Space.relation B S hS (subι s t r hrs G ≫ s) (subι s t r hrs G ≫ t)) := by
    intro T
    refine ⟨fun a ↦ ?_, fun {a b} hab ↦ ?_, fun {a b c} hab hbc ↦ ?_⟩
    · exact (rel_iff r hrt hrs G a a).2 ⟨(hpre T).refl a, fun p ↦ .inr (AgreeNear.refl a p)⟩
    · obtain ⟨h₁, h₂⟩ := (rel_iff r hrt hrs G a b).1 hab
      exact (rel_iff r hrt hrs G b a).2 ⟨(hpre T).symm h₁, fun p ↦
        (h₂ p).elim (fun h ↦ .inl ⟨h.2, h.1⟩) (fun h ↦ .inr h.symm)⟩
    · obtain ⟨h₁, h₂⟩ := (rel_iff r hrt hrs G a b).1 hab
      obtain ⟨h₃, h₄⟩ := (rel_iff r hrt hrs G b c).1 hbc
      refine (rel_iff r hrt hrs G a c).2 ⟨(hpre T).trans h₁ h₃, fun p ↦ ?_⟩
      by_cases hac : a.left p ∈ G ∧ c.left p ∈ G
      · exact .inl hac
      · right
        rcases h₂ p with hab' | hab' <;> rcases h₄ p with hbc' | hbc'
        · exact absurd ⟨hab'.1, hbc'.2⟩ hac
        · refine absurd ⟨hab'.1, ?_⟩ hac
          rw [← hbc'.apply_eq]
          exact hab'.2
        · refine absurd ⟨?_, hbc'.2⟩ hac
          rw [hab'.apply_eq]
          exact hbc'.1
        · exact hab'.trans hbc'
  have hequiv := (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).2
    ⟨hmono', hpre'⟩
  have hetS := etale_map_source_left (s := s) (t := t)
  have hetT := etale_map_target_left (s := s) (t := t)
  have hs' : Etale (Space.relation B S hS (subι s t r hrs G ≫ s)
      (subι s t r hrs G ≫ t)).source.left := by
    rw [TwistedAffineLine.relation_source_eq]
    change Etale ((opens s t r hrs G).ι ≫ ((Over.post B.inclusion).map s).left)
    exact MorphismProperty.comp_mem @Etale _ _ inferInstance hetS
  have ht' : Etale (Space.relation B S hS (subι s t r hrs G ≫ s)
      (subι s t r hrs G ≫ t)).target.left := by
    rw [TwistedAffineLine.relation_target_eq]
    change Etale ((opens s t r hrs G).ι ≫ ((Over.post B.inclusion).map t).left)
    exact MorphismProperty.comp_mem @Etale _ _ inferInstance hetT
  exact @IsEtaleEquivalenceRelation.mk _ _ _ _ hequiv hs' ht'

/-! ### Points of the open subrelation -/

/-- A point of `R` both of whose projections lie in `G` is a point of the open subrelation. -/
theorem exists_subι_apply_eq (G : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ε : (BigFppfOver.toScheme B S hS).obj R) (hεt : (BigFppfOver.toScheme B S hS).map t ε ∈ G)
    (hεs : (BigFppfOver.toScheme B S hS).map s ε ∈ G) :
    ∃ ε' : (BigFppfOver.toScheme B S hS).obj (subObject s t r hrs G),
      (BigFppfOver.toScheme B S hS).map (subι s t r hrs G) ε' = ε :=
  ⟨⟨ε, Or.inr ⟨hεt, hεs⟩⟩, rfl⟩

include hrt in
/-- **Away from `G` the open subrelation is the diagonal**: near a point of the open subrelation
one of whose projections leaves `G`, the two projections agree. -/
theorem exists_isOpen_forall_eq (G : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ε : (BigFppfOver.toScheme B S hS).obj (subObject s t r hrs G))
    (hε : (BigFppfOver.toScheme B S hS).map (subι s t r hrs G ≫ s) ε ∉ G ∨
      (BigFppfOver.toScheme B S hS).map (subι s t r hrs G ≫ t) ε ∉ G) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj (subObject s t r hrs G)), IsOpen V ∧ ε ∈ V ∧
      ∀ ε' ∈ V, (BigFppfOver.toScheme B S hS).map (subι s t r hrs G ≫ s) ε' =
        (BigFppfOver.toScheme B S hS).map (subι s t r hrs G ≫ t) ε' := by
  have := isOpenImmersion_identitySection (t := t) r hrs
  have hrange : (opens s t r hrs G).ι ε ∈ Set.range r.left := by
    rcases (mem_opens_iff s t r hrs G _).1 ((opens s t r hrs G).ι_apply ε ▸ ε.2) with h | ⟨ht, hs⟩
    · exact h
    · exact absurd hε (by rw [not_or, not_not, not_not]; exact ⟨hs, ht⟩)
  refine ⟨(opens s t r hrs G).ι ⁻¹' Set.range r.left,
    r.left.isOpenEmbedding.isOpen_range.preimage (opens s t r hrs G).ι.continuous, hrange,
    fun ε' hε' ↦ ?_⟩
  obtain ⟨v, hv⟩ := hε'
  change ((Over.post B.inclusion).map s).left ((opens s t r hrs G).ι ε') =
    ((Over.post B.inclusion).map t).left ((opens s t r hrs G).ι ε')
  have hv' : r.left v = (opens s t r hrs G).ι ε' := hv
  rw [← hv', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    identitySection_left_comp r s hrs, identitySection_left_comp r t hrt]

end AlgebraicGeometry.Space.OpenSubRelation

end
