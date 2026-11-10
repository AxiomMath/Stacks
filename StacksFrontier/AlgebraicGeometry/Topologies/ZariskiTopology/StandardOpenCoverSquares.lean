module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Standard open cover squares of affine opens, and the almost chaotic topology

Let `B` be a big Zariski site containing a scheme `S`. A *standard open cover square* of affine
opens of `S` is a cartesian square whose two maps to the bottom right corner are, up to
isomorphism, a pair of standard opens covering that corner. Such a square generates a covering
sieve for the Zariski topology on affine opens, is cartesian, every sheaf of sets takes it to a
cartesian square of sections, and its sheafified representables form a pushout square.

The *almost chaotic* topology on the affine opens of `S` is the topology in which an empty
affine open is covered by the empty family and no other affine open has a covering sieve besides
the maximal one. It lies between the trivial topology and the Zariski topology, and in it, as in
the Zariski topology, the empty sieve covers an empty affine open.

## Main definitions

* `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare` — the configuration of a pair
  of standard opens covering an affine open, with their intersection as the fourth corner.
* `AlgebraicGeometry.SmallAffineZariski.almostChaotic` — the almost chaotic topology.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare.ofTwoArrows_mem_topology` — a
  standard open cover square generates a Zariski covering sieve.
* `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare.isPullback` and
  `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare.op_map_isPullback` — the square
  is cartesian, and so is its image under any sheaf of sets.
* `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare.isPushout_sheafifiedYoneda` and
  `AlgebraicGeometry.SmallAffineZariski.IsStandardOpenCoverSquare.mono_sheafifiedYoneda_map_f₁₂` —
  the sheafified representables of such a square form a pushout square with monomorphic edge.
* `AlgebraicGeometry.SmallAffineZariski.trivial_le_almostChaotic` and
  `AlgebraicGeometry.SmallAffineZariski.almostChaotic_le_topology` — the almost chaotic topology
  is intermediate between the trivial and the Zariski topology.

## References

* [Stacks Project, Tag 00VJ](https://stacks.math.columbia.edu/tag/00VJ)
* [Stacks Project, Tag 0F1L](https://stacks.math.columbia.edu/tag/0F1L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

/-- The index type of the image of a family of morphisms under a functor is the index type of
that family. -/
private instance {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {T : C}
    {E : PreZeroHypercover.{w} T} (F : C ⥤ D) [IsEmpty E.I₀] : IsEmpty (E.map F).I₀ :=
  inferInstanceAs (IsEmpty E.I₀)

/-- The index type of the image of a family of morphisms under a functor is the index type of
that family. -/
private instance {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {T : C}
    {E : PreZeroHypercover.{w} T} (F : C ⥤ D) [Finite E.I₀] : Finite (E.map F).I₀ :=
  inferInstanceAs (Finite E.I₀)

/-- Two maps out of a common source into the values of a presheaf over `X₂` and `X₃` that agree
after restriction along `f₁₂ : X₁ ⟶ X₂` and `f₁₃ : X₁ ⟶ X₃` still agree after further
restriction along any `t : T ⟶ X₁`. -/
private lemma comp_map_op_comp {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
    (F : Cᵒᵖ ⥤ D) {X₁ X₂ X₃ T : C} (f₁₂ : X₁ ⟶ X₂) (f₁₃ : X₁ ⟶ X₃) {E : D}
    {x : E ⟶ F.obj (op X₂)} {y : E ⟶ F.obj (op X₃)}
    (hxy : x ≫ F.map f₁₂.op = y ≫ F.map f₁₃.op) (t : T ⟶ X₁) :
    x ≫ F.map (t ≫ f₁₂).op = y ≫ F.map (t ≫ f₁₃).op := by
  rw [op_comp, op_comp, F.map_comp, F.map_comp, ← Category.assoc, ← Category.assoc, hxy]

end CategoryTheory

namespace AlgebraicGeometry

/-- A family of morphisms with empty index type into an empty scheme is a Zariski covering. -/
private lemma presieve₀_mem_zariskiPrecoverage_of_isEmpty {T : Scheme.{u}} (hT : IsEmpty T)
    {E : PreZeroHypercover.{w} T} (hE : IsEmpty E.I₀) :
    E.presieve₀ ∈ Scheme.zariskiPrecoverage T := by
  have := hT
  have := hE
  rw [show E.presieve₀ = ⊥ from Presieve.ofArrows_of_isEmpty _]
  exact Scheme.bot_mem_precoverage _ T

namespace SmallAffineZariski

section Covering

variable {B : BigZariskiSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A finite family of standard opens of an affine open `U` of `S` that covers `U` generates a
Zariski covering sieve of `U`: the family is combinatorially equivalent to a selected covering
family of the big site, and deduplicating it along that equivalence keeps it finite and
standard while shrinking its index type into the selected one. -/
public lemma generate_mem_topology_of_standardCover {U : SmallAffineZariski B S hS}
    (E : PreZeroHypercover.{u + 1} U)
    (hcover : (E.map (toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((toScheme B S hS).obj U))
    (hfinite : Finite E.I₀)
    (hstandard : ∀ i, ∃ f : Γ((toScheme B S hS).obj U, ⊤),
      ∃ e : (toScheme B S hS).obj (E.X i) ≅
        (((toScheme B S hS).obj U).basicOpen f).toScheme,
      (toScheme B S hS).map (E.f i) =
        e.hom ≫ (((toScheme B S hS).obj U).basicOpen f).ι) :
    Sieve.generate E.presieve₀ ∈ topology B S hS U := by
  have := hfinite
  let K := inclusion B S hS ⋙ SmallZariski.inclusion B S hS ⋙ BigZariskiOver.inclusion B S hS
  have hz : IsZariskiCovering ⟨K.obj U, E.map K⟩ := hcover
  obtain ⟨⟨target, representative⟩, hbounded, hcomb⟩ :=
    B.covering_representative ⟨K.obj U, E.map K⟩ hz
  obtain ⟨targeteq, hcomb⟩ := hcomb
  cases targeteq
  change (E.map K).CombinatoriallyEquivalent representative at hcomb
  obtain ⟨indices, sourceeq, arroweq⟩ := hcomb.2
  let refined : PreZeroHypercover.{u + 1} U :=
    ⟨Set.range indices, fun i => E.X i.val, fun i => E.f i.val⟩
  have hmap : (refined.map K).presieve₀ = representative.presieve₀ := by
    apply le_antisymm
    · rintro T a ⟨i⟩
      obtain ⟨i', hi'⟩ := i.property
      change representative.presieve₀ (K.map (E.f i.val))
      rw [← hi']
      refine representative.presieve₀_of_eq i' _ (sourceeq i').symm ?_
      have harrow := (eqToHom (sourceeq i').symm ≫= arroweq i').symm
      rwa [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at harrow
    · rintro T a ⟨i⟩
      exact (refined.map K).presieve₀_of_eq ⟨indices i, ⟨i, rfl⟩⟩ _
        (sourceeq i) (arroweq i)
  have hrefinedZariski :
      ((refined.map K).map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology _ := by
    rw [PreZeroHypercover.presieve₀_map, hmap, ← PreZeroHypercover.presieve₀_map]
    exact hbounded.1
  have hrefined : IsCovering B S hS ⟨U, refined⟩ :=
    ⟨⟨hrefinedZariski, Cardinal.mk_range_le.trans hbounded.2⟩, hrefinedZariski,
      Finite.of_injective (fun i : Set.range indices => i.val) Subtype.val_injective,
      fun i => hstandard i.val⟩
  refine (topology B S hS).superset_covering
    (Sieve.generate_mono (show refined.presieve₀ ≤ E.presieve₀ from ?_)) ?_
  · rintro T a ⟨i⟩
    exact ⟨i.val⟩
  · exact Precoverage.generate_mem_toGrothendieck ⟨refined, rfl, hrefined⟩

end Covering

section Squares

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A square of affine opens of `S` is a standard open cover square when it is cartesian and its
two maps to the bottom right corner `U` are isomorphic to the inclusions of two standard opens
of `U` whose union is `U`. -/
public def IsStandardOpenCoverSquare (sq : Square (SmallAffineZariski B S hS)) : Prop :=
  ∃ f g : Γ((toScheme B S hS).obj sq.X₄, ⊤),
    ∃ eV : (toScheme B S hS).obj sq.X₂ ≅
        (((toScheme B S hS).obj sq.X₄).basicOpen f).toScheme,
      ∃ eW : (toScheme B S hS).obj sq.X₃ ≅
          (((toScheme B S hS).obj sq.X₄).basicOpen g).toScheme,
        (toScheme B S hS).map sq.f₂₄ =
            eV.hom ≫ (((toScheme B S hS).obj sq.X₄).basicOpen f).ι ∧
          (toScheme B S hS).map sq.f₃₄ =
            eW.hom ≫ (((toScheme B S hS).obj sq.X₄).basicOpen g).ι ∧
          ((toScheme B S hS).obj sq.X₄).basicOpen f ⊔
            ((toScheme B S hS).obj sq.X₄).basicOpen g = ⊤ ∧
          (sq.map (toScheme B S hS)).IsPullback

end Squares

namespace IsStandardOpenCoverSquare

variable {B : BigZariskiSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {sq : Square (SmallAffineZariski B S hS)}

/-- The first of the two maps of a standard open cover square to its bottom right corner is an
open immersion. -/
public lemma isOpenImmersion_map_f₂₄ (hsq : IsStandardOpenCoverSquare B S hS sq) :
    IsOpenImmersion ((toScheme B S hS).map sq.f₂₄) := by
  obtain ⟨f, g, eV, eW, hV, hW, hcov, hpull⟩ := hsq
  rw [hV]
  infer_instance

/-- The second of the two maps of a standard open cover square to its bottom right corner is an
open immersion. -/
public lemma isOpenImmersion_map_f₃₄ (hsq : IsStandardOpenCoverSquare B S hS sq) :
    IsOpenImmersion ((toScheme B S hS).map sq.f₃₄) := by
  obtain ⟨f, g, eV, eW, hV, hW, hcov, hpull⟩ := hsq
  rw [hW]
  infer_instance

/-- The top map of a standard open cover square is a monomorphism, being a base change of an
open immersion. -/
public lemma mono_f₁₂ (hsq : IsStandardOpenCoverSquare B S hS sq) : Mono sq.f₁₂ := by
  have himm := hsq.isOpenImmersion_map_f₃₄
  obtain ⟨f, g, eV, eW, hV, hW, hcov, hpull⟩ := hsq
  have : IsOpenImmersion ((toScheme B S hS).map sq.f₁₂) :=
    MorphismProperty.of_isPullback hpull.flip himm
  exact (toScheme B S hS).mono_of_mono_map inferInstance

/-- The right map of a standard open cover square is a monomorphism. -/
public lemma mono_f₂₄ (hsq : IsStandardOpenCoverSquare B S hS sq) : Mono sq.f₂₄ := by
  have := hsq.isOpenImmersion_map_f₂₄
  exact (toScheme B S hS).mono_of_mono_map (by infer_instance)

/-- The bottom map of a standard open cover square is a monomorphism. -/
public lemma mono_f₃₄ (hsq : IsStandardOpenCoverSquare B S hS sq) : Mono sq.f₃₄ := by
  have := hsq.isOpenImmersion_map_f₃₄
  exact (toScheme B S hS).mono_of_mono_map (by infer_instance)

/-- A standard open cover square is cartesian: it is cartesian after passing to schemes, and the
functor to schemes reflects isomorphisms. -/
public lemma isPullback (hsq : IsStandardOpenCoverSquare B S hS sq) : sq.IsPullback := by
  have : ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) (toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  obtain ⟨f, g, eV, eW, hV, hW, hcov, hpull⟩ := hsq
  exact hpull.of_map (toScheme B S hS)

/-- The two standard opens of a standard open cover square generate a Zariski covering sieve of
its bottom right corner. -/
public lemma ofTwoArrows_mem_topology (hsq : IsStandardOpenCoverSquare B S hS sq) :
    Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ topology B S hS sq.X₄ := by
  have himmV := hsq.isOpenImmersion_map_f₂₄
  have himmW := hsq.isOpenImmersion_map_f₃₄
  obtain ⟨f, g, eV, eW, hV, hW, hcov, hpull⟩ := hsq
  let family : PreZeroHypercover.{u + 1} sq.X₄ :=
    ⟨ULift WalkingPair, fun i => WalkingPair.casesOn i.down sq.X₂ sq.X₃,
      fun i => WalkingPair.casesOn i.down sq.f₂₄ sq.f₃₄⟩
  have hrange : ∀ {X : Scheme.{u}} {V : ((toScheme B S hS).obj sq.X₄).Opens}
      (φ : X ⟶ (toScheme B S hS).obj sq.X₄) [IsOpenImmersion φ] (e : X ≅ V.toScheme),
      φ = e.hom ≫ V.ι → φ.opensRange = V := by
    intro X V φ _ e h
    subst h
    apply TopologicalSpace.Opens.ext
    change Set.range (V.ι ∘ e.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr e.hom.surjective, Set.image_univ]
    exact congrArg (fun W : ((toScheme B S hS).obj sq.X₄).Opens => W.carrier)
      (Scheme.Opens.opensRange_ι V)
  have hcoverFamily : (family.map (toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage _ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · have hx : x ∈ ((toScheme B S hS).map sq.f₂₄).opensRange ⊔
          ((toScheme B S hS).map sq.f₃₄).opensRange := by
        rw [hrange _ eV hV, hrange _ eW hW, hcov]
        trivial
      rcases hx with hx | hx
      · exact ⟨⟨WalkingPair.left⟩, hx⟩
      · exact ⟨⟨WalkingPair.right⟩, hx⟩
    · rintro ⟨(_ | _)⟩
      exacts [himmV, himmW]
  refine (topology B S hS).superset_covering
    (Sieve.generate_mono (show family.presieve₀ ≤
      Presieve.ofArrows (pairFunction sq.X₂ sq.X₃)
        (fun i => WalkingPair.casesOn i sq.f₂₄ sq.f₃₄) from ?_)) ?_
  · rintro T a ⟨⟨(_ | _)⟩⟩
    exacts [⟨WalkingPair.left⟩, ⟨WalkingPair.right⟩]
  · refine generate_mem_topology_of_standardCover family hcoverFamily inferInstance ?_
    rintro ⟨(_ | _)⟩
    exacts [⟨f, eV, hV⟩, ⟨g, eW, hW⟩]

/-- Every sheaf of sets on the affine opens of `S` takes a standard open cover square to a
cartesian square of sections: two sections over the two standard opens that agree on the fourth
corner amalgamate uniquely over their union. -/
public lemma op_map_isPullback (hsq : IsStandardOpenCoverSquare B S hS sq)
    (F : Sheaf (topology B S hS) (Type (u + 1))) : (sq.op.map F.obj).IsPullback := by
  have hcovering := hsq.ofTwoArrows_mem_topology
  have hmono₂₄ : Mono sq.f₂₄ := hsq.mono_f₂₄
  have hmono₃₄ : Mono sq.f₃₄ := hsq.mono_f₃₄
  have hpullback := hsq.isPullback
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun c => F.property.amalgamateOfArrows _ hcovering
      (fun i => WalkingPair.casesOn i c.fst c.snd) (fun T => ?_)) ?_ ?_ ?_
  · rintro (_ | _) (_ | _) a b hab
    · obtain rfl : a = b := (cancel_mono sq.f₂₄).mp hab
      rfl
    · obtain ⟨c', rfl, rfl⟩ := PullbackCone.IsLimit.lift' hpullback.isLimit _ _ hab
      have hc : c.fst ≫ F.obj.map sq.f₁₂.op = c.snd ≫ F.obj.map sq.f₁₃.op := c.condition
      exact comp_map_op_comp F.obj sq.f₁₂ sq.f₁₃ hc c'
    · obtain ⟨c', rfl, rfl⟩ := PullbackCone.IsLimit.lift' hpullback.isLimit _ _ hab.symm
      have hc : c.snd ≫ F.obj.map sq.f₁₃.op = c.fst ≫ F.obj.map sq.f₁₂.op := c.condition.symm
      exact comp_map_op_comp F.obj sq.f₁₃ sq.f₁₂ hc c'
    · obtain rfl : a = b := (cancel_mono sq.f₃₄).mp hab
      rfl
  · intro c
    exact F.property.amalgamateOfArrows_map _ hcovering _ _ WalkingPair.left
  · intro c
    exact F.property.amalgamateOfArrows_map _ hcovering _ _ WalkingPair.right
  · intro c a hfst hsnd
    apply F.property.hom_ext_ofArrows _ hcovering
    rintro (_ | _)
    · rwa [F.property.amalgamateOfArrows_map _ hcovering _ _ WalkingPair.left]
    · rwa [F.property.amalgamateOfArrows_map _ hcovering _ _ WalkingPair.right]

/-- The sheafified representables of a standard open cover square form a pushout square: by
Yoneda's lemma for sheaves this is the statement that every sheaf of sets takes the square to a
cartesian square of sections. -/
public lemma isPushout_sheafifiedYoneda (hsq : IsStandardOpenCoverSquare B S hS sq) :
    (sq.map (Sheaf.sheafifiedYoneda (topology B S hS))).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro F
  refine (Square.IsPullback.iff_of_equiv _ (sq.op.map F.obj)
    (Sheaf.sectionEquiv (topology B S hS)) (Sheaf.sectionEquiv (topology B S hS))
    (Sheaf.sectionEquiv (topology B S hS)) (Sheaf.sectionEquiv (topology B S hS))
    ?_ ?_ ?_ ?_).mpr (hsq.op_map_isPullback F)
  all_goals ext a; exact Sheaf.sectionEquiv_map_comp (topology B S hS) _ a

/-- The top map of a standard open cover square stays a monomorphism after sheafified Yoneda. -/
public lemma mono_sheafifiedYoneda_map_f₁₂ (hsq : IsStandardOpenCoverSquare B S hS sq) :
    Mono ((Sheaf.sheafifiedYoneda (topology B S hS)).map sq.f₁₂) := by
  have := hsq.mono_f₁₂
  exact Sheaf.mono_sheafifiedYoneda_map _

end IsStandardOpenCoverSquare

section AlmostChaotic

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The almost chaotic topology on the affine opens of `S`: an empty affine open is covered by
every sieve, in particular by the empty one, and every other affine open only by the maximal
sieve. -/
public def almostChaotic : GrothendieckTopology (SmallAffineZariski B S hS) where
  sieves U := {T | IsEmpty ((toScheme B S hS).obj U) ∨ T = ⊤}
  top_mem' _ := Or.inr rfl
  pullback_stable' U V T a hT := by
    rcases hT with hU | rfl
    · have := hU
      exact Or.inl ((toScheme B S hS).map a).base.hom.1.isEmpty
    · exact Or.inr (by ext b; simp)
  transitive' U T hT R hR := by
    rcases hT with hU | rfl
    · exact Or.inl hU
    · rcases hR (show (⊤ : Sieve U) (𝟙 U) by simp) with hU | hR'
      · exact Or.inl hU
      · exact Or.inr (Sieve.pullback_id.symm.trans hR')

/-- A sieve is almost chaotic covering exactly when its affine open is empty or it is the maximal
sieve. -/
public lemma mem_almostChaotic_iff {U : SmallAffineZariski B S hS} {T : Sieve U} :
    T ∈ almostChaotic B S hS U ↔ IsEmpty ((toScheme B S hS).obj U) ∨ T = ⊤ :=
  Iff.rfl

/-- The almost chaotic topology is finer than the trivial topology. -/
public lemma trivial_le_almostChaotic :
    GrothendieckTopology.trivial (SmallAffineZariski B S hS) ≤ almostChaotic B S hS :=
  bot_le

/-- The empty sieve covers an empty affine open in the almost chaotic topology. -/
public lemma bot_mem_almostChaotic {U : SmallAffineZariski B S hS}
    (hU : IsEmpty ((toScheme B S hS).obj U)) : (⊥ : Sieve U) ∈ almostChaotic B S hS U :=
  Or.inl hU

/-- The empty sieve covers an empty affine open in the Zariski topology: the empty family is a
standard Zariski covering of an empty affine scheme. -/
public lemma bot_mem_topology {U : SmallAffineZariski B S hS}
    (hU : IsEmpty ((toScheme B S hS).obj U)) : (⊥ : Sieve U) ∈ topology B S hS U := by
  rw [← Sieve.generate_bot]
  apply Precoverage.generate_mem_toGrothendieck
  rw [mem_precoverage_iff]
  refine ⟨PreZeroHypercover.empty U, by simp, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact presieve₀_mem_zariskiPrecoverage_of_isEmpty hU inferInstance
  · exact le_of_eq_of_le (Cardinal.mk_eq_zero_iff.mpr inferInstance) zero_le
  · exact presieve₀_mem_zariskiPrecoverage_of_isEmpty hU inferInstance
  · exact inferInstance
  · exact isEmptyElim

/-- The Zariski topology is finer than the almost chaotic topology. -/
public lemma almostChaotic_le_topology : almostChaotic B S hS ≤ topology B S hS := by
  intro U T hT
  rcases hT with hU | rfl
  · exact (topology B S hS).superset_covering (bot_le : (⊥ : Sieve U) ≤ T)
      (bot_mem_topology B S hS hU)
  · exact (topology B S hS).top_mem U

end AlmostChaotic

end SmallAffineZariski

end AlgebraicGeometry

end
