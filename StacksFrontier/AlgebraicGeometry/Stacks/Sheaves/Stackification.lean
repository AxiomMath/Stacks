module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Stackification does not change the fppf topos

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`. If `f` induces an equivalence of stackifications, then the morphism of topoi
`Sh(𝒳_fppf) ⟶ Sh(𝒴_fppf)` of Stacks 06TS is an equivalence.

This file proves the conclusion under the two local clauses of Stacks 02ZN on `f` itself,
gathered in `CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence`: on every
fibre the induced maps of morphism presheaves are locally injective and locally surjective, and
every object of a fibre of the target is, along a covering sieve, in the essential image. The
hypothesis of the source — stackifications `𝒳 ⥤ 𝒳'` and `𝒴 ⥤ 𝒴'` and an equivalence
`𝒳' ⥤ 𝒴'` over the site compatible with `f` — is reduced to these clauses, and Stacks 06WQ
registered, in `StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationInduced`.

From those two clauses the 1-morphism is shown to be a dense subsite inclusion for the
inherited topologies of Stacks 06TP — cover-dense, locally full and locally faithful — and the
inverse image of the induced morphism of topoi is restriction along it, so it is an equivalence.

## Main definitions

* `CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence`: the two local
  clauses of Stacks 02ZN for a 1-morphism `f`, which a 1-morphism inducing an equivalence of
  stackifications satisfies.

## Main results

* `CategoryTheory.Functor.mem_inheritedTopology_functorPullback`: a covering sieve of the base
  pulls back along a fibred functor to a covering sieve for the inherited topology.
* `CategoryTheory.Functor.IsFibredOneMorphism.isDenseSubsite_of_isStackificationEquivalence`:
  a 1-morphism inducing an equivalence of stackifications is a dense subsite inclusion for the
  inherited topologies.
* `AlgebraicGeometry.Stack.isEquivalence_inverseImage_of_isStackificationEquivalence`: the
  inverse image of the induced morphism of fppf topoi is an equivalence, under the two local
  clauses. Stacks 06WQ itself, under the hypothesis of the source, is
  `AlgebraicGeometry.Stack.isEquivalence_inverseImage_of_isEquivalenceOver_stackifications`.

## Implementation notes

The three local conditions are proved by one and the same move: the criterion of Stacks 02ZN
produces a covering sieve of the *base*, and
`CategoryTheory.Functor.mem_inheritedTopology_functorPullback` turns it into a covering sieve
for the inherited topology, whose members are the strongly cartesian lifts of its members. Over
such a lift the required morphism of `𝒳` is assembled from the lift supplied by the criterion,
and uniqueness of lifts of a strongly cartesian morphism is what identifies two such
assemblies.

Local faithfulness is the only one of the three that has to move between a fibre and the whole
category: two parallel arrows of `𝒳` with equal images lie over one and the same arrow of the
base, so they are determined by arrows of a fibre into a chosen cartesian lift, and the
criterion applies to those.

The statement is for an arbitrary topology on the underlying category of schemes wherever the
argument allows, and is specialized to the fppf topology only in the tagged result, which is
where the source states it.

The underlying object of an object of a fibre is a projection out of a subtype, so the
intermediate goals of the three proofs mention subterms that only typecheck once the definition
of `CategoryTheory.Functor.Fiber` is unfolded. Such goals are therefore manipulated by
composing equalities rather than by rewriting, and the two steps that are genuinely about
rewriting are isolated as `CategoryTheory.comp_eq_comp_of_fac` and
`CategoryTheory.Functor.map_comp_eq_eqToHom_comp`, whose statements speak only of a category
and a functor.

## References

* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 06TS](https://stacks.math.columbia.edu/tag/06TS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u uC v₁ v₂ w t

namespace CategoryTheory

/-- If `g` factors as `u ≫ m`, and `a` and `b` factor as `α ≫ v` and `β ≫ v` through two
morphisms that `m` cannot tell apart, then `g` cannot tell `a` and `b` apart either. -/
theorem comp_eq_comp_of_fac {D : Type*} [Category D] {Z P A B Q : D} {g : Z ⟶ A} {a b : A ⟶ B}
    (u : Z ⟶ P) (m : P ⟶ A) (hu : u ≫ m = g) {α β : A ⟶ Q} (v : Q ⟶ B) (hm : m ≫ α = m ≫ β)
    (ha : α ≫ v = a) (hb : β ≫ v = b) : g ≫ a = g ≫ b := by
  subst hu ha hb
  simp [reassoc_of% hm]

end CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{w} C] {X : Type v₁} [Category.{w} X]
  {Y : Type v₂} [Category.{w} Y]

/-- The image in the base of a morphism lying over an identity followed by a morphism lying over
`k` is `k` itself, up to the identification of the base of the domain with the source of `k`. -/
theorem map_comp_eq_eqToHom_comp {D : Type*} [Category D] {E : Type*} [Category E] (π : D ⥤ E)
    {V : E} {d e f : D} (φ : d ⟶ e) (ψ : e ⟶ f) {k : V ⟶ π.obj f}
    (hφ : π.IsHomLift (𝟙 V) φ) (hψ : π.IsHomLift k ψ) (h : π.obj d = V) :
    π.map (φ ≫ ψ) = eqToHom h ≫ k := by
  rw [π.map_comp, IsHomLift.fac' π (𝟙 V) φ, IsHomLift.fac' π k ψ]
  simp

/-- If strongly cartesian arrows into `a` have images generating a covering sieve, they generate a
covering sieve for the inherited topology. -/
private theorem generate_ofArrows_mem_inheritedTopology (r : X ⥤ C) [r.IsFibered]
    (J : GrothendieckTopology C) {a : X} {I : Type*} {Z : I → X} (g : ∀ i, Z i ⟶ a)
    (hg : ∀ i, r.IsStronglyCartesian (r.map (g i)) (g i))
    (h : Sieve.ofArrows (fun i => r.obj (Z i)) (fun i => r.map (g i)) ∈ J (r.obj a)) :
    Sieve.generate (Presieve.ofArrows Z g) ∈ r.inheritedTopology J a := by
  rw [Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, ?_⟩
  · rintro W k ⟨i⟩
    exact hg i
  · rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    exact h

/-- A covering sieve of the base pulls back, along a fibred functor, to a covering sieve for the
inherited topology of Stacks 06NV: its strongly cartesian lifts form an inherited covering
family, and each of them is in the pullback. -/
theorem mem_inheritedTopology_functorPullback (r : X ⥤ C) [r.IsFibered]
    (J : GrothendieckTopology C) (a : X) {R : Sieve (r.obj a)} (hR : R ∈ J (r.obj a)) :
    R.functorPullback r ∈ r.inheritedTopology J a := by
  let I : Type (max v₁ w) :=
    Σ c : X, {h : c ⟶ a // r.IsStronglyCartesian (r.map h) h ∧ R.arrows (r.map h)}
  let Z : I → X := fun i => i.1
  let g : ∀ i, Z i ⟶ a := fun i => i.2.1
  have himg : Sieve.ofArrows (fun i => r.obj (Z i)) (fun i => r.map (g i)) = R := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro W u ⟨i⟩
      exact i.2.2.2
    · intro V k hk
      obtain ⟨c, h, hc⟩ := CategoryTheory.Functor.IsPreFibered.exists_isCartesian' k
      have : r.IsCartesian k h := hc
      have : r.IsStronglyCartesian k h := inferInstance
      obtain rfl : r.obj c = V := IsHomLift.domain_eq r k h
      obtain rfl : k = r.map h := IsHomLift.eq_of_isHomLift r k h
      exact Sieve.ofArrows_mk _ _ (⟨c, h, inferInstance, hk⟩ : I)
  refine (r.inheritedTopology J).superset_covering ?_
    (generate_ofArrows_mem_inheritedTopology r J g (fun i => i.2.2.1) (himg ▸ hR))
  rw [Sieve.generate_le_iff]
  rintro V k ⟨i⟩
  exact i.2.2.2

namespace IsFibredOneMorphism

variable {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered] {F : X ⥤ Y}

/-- An arrow `g` lying over the same base arrow as `f` factors through the chosen cartesian lift
of `p.map f`, by an arrow lying over an identity. -/
private theorem exists_comp_pullbackMap_eq (hp : p.IsFiberedInGroupoids) {A B : X} (f g : A ⟶ B)
    [p.IsHomLift (p.map f) g] :
    ∃ v : A ⟶ Functor.IsPreFibered.pullbackObj (rfl : p.obj B = p.obj B) (p.map f),
      p.IsHomLift (𝟙 (p.obj A)) v ∧
        v ≫ Functor.IsPreFibered.pullbackMap (rfl : p.obj B = p.obj B) (p.map f) = g := by
  have hone : p.map f = 𝟙 _ ≫ p.map f := by simp
  have := hp.isStronglyCartesian_homLift (p.map f)
    (Functor.IsPreFibered.pullbackMap (rfl : p.obj B = p.obj B) (p.map f))
  exact ⟨_, inferInstance, Functor.IsStronglyCartesian.fac p (p.map f) _ hone g⟩

/-- The two local clauses of Stacks 02ZN for a 1-morphism `F` of fibred categories over a site:
on every fibre the induced map of morphism presheaves is locally injective and locally
surjective, and every object of a fibre of the target is, along a covering sieve of the base, in
the essential image of `F` on fibres.

This is not itself the statement that `F` induces an equivalence of stackifications, which
speaks of stackifications of source and target; a 1-morphism into a category fibred in groupoids
which does induce one satisfies these clauses, by
`CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence_of_isEquivalenceOver`.
The second clause is
`CategoryTheory.Functor.LocallyEssSurjOnFibers`, spelled with
`CategoryTheory.Functor.fiberFunctorOfCompEq` rather than
`CategoryTheory.Functor.Fiber.mapOfComp` because that is the spelling the criteria of
Stacks 04WR are stated in. -/
def IsStackificationEquivalence (hF : p.IsFibredOneMorphism q F)
    (J : GrothendieckTopology C) : Prop :=
  (∀ (U : C) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap x y)) ∧
    (∀ (U : C) (y : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V : C⦄ ⦃k : V ⟶ U⦄,
      R.arrows k →
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).essImage
          (Functor.pullbackFiber q y k))

variable (J : GrothendieckTopology C)

/-- **Locally full.** A 1-morphism inducing an equivalence of stackifications is locally full
for the inherited topologies: an arrow between the images of two objects of `𝒳` is in the image
of `F` along a covering sieve.

The surjectivity half of clause (1) of Stacks 02ZN gives a covering sieve of the base along
which the arrow lifts; its strongly cartesian lifts cover the source, and over each of them the
lift is composed with the comparison map of the chosen cartesian lift. -/
theorem imageSieve_mem_inheritedTopology [HasPullbacks C] (hp : p.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence J)
    ⦃A Bb : X⦄ (c : F.obj A ⟶ F.obj Bb) :
    F.imageSieve c ∈ p.inheritedTopology J A := by
  obtain ⟨R, hR, hlift⟩ := CategoryTheory.exists_covering_lift_hom hF J heq.1 c
  refine (p.inheritedTopology J).superset_covering ?_
    (mem_inheritedTopology_functorPullback p J A hR)
  intro Z g hg
  change R.arrows (p.map g) at hg
  obtain ⟨wlift, hw⟩ := hlift (p.map g) hg
  obtain ⟨v, -, hv⟩ := exists_comp_pullbackMap_eq hp g g
  refine ⟨v ≫ wlift, ?_⟩
  exact (F.map_comp v wlift).trans ((congrArg (F.map v ≫ ·) hw.symm).trans
    ((Category.assoc _ _ c).symm.trans
      (congrArg (· ≫ c) ((F.map_comp v _).symm.trans (congrArg F.map hv)))))

/-- **Locally faithful.** A 1-morphism inducing an equivalence of stackifications is locally
faithful for the inherited topologies: two parallel arrows of `𝒳` with the same image agree
along a covering sieve.

The two arrows lie over one and the same arrow `f` of the base, because `F` commutes with the
structure functors and is injective on the base by fibredness of the target; so each of them is
the comparison map of a chosen cartesian lift of `f` composed with an arrow of a fibre, and the
injectivity half of clause (1) of Stacks 02ZN applies to those two arrows of the fibre. -/
theorem equalizerSieve_mem_inheritedTopology (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (hF : p.IsFibredOneMorphism q F)
    (heq : hF.IsStackificationEquivalence J)
    {A Bb : X} (a b : A ⟶ Bb) (hab : F.map a = F.map b) :
    Sieve.equalizer a b ∈ p.inheritedTopology J A := by
  have hf : p.map b = p.map a := by
    rw [Functor.map_eq_of_comp_eq p q F hF.comp_eq a,
      Functor.map_eq_of_comp_eq p q F hF.comp_eq b, hab]
  have hbLift : p.IsHomLift (p.map a) b := Functor.isHomLift_of_eq (IsHomLift.map b) hf
  let x : p.Fiber (p.obj A) := Functor.Fiber.mk rfl
  let y : p.Fiber (p.obj A) := Functor.Fiber.mk
    (Functor.IsPreFibered.pullbackObj_proj (rfl : p.obj Bb = p.obj Bb) (p.map a))
  let cart : Functor.Fiber.fiberInclusion.obj y ⟶ Bb :=
    Functor.IsPreFibered.pullbackMap (rfl : p.obj Bb = p.obj Bb) (p.map a)
  obtain ⟨vα, hvα, hαfac'⟩ := exists_comp_pullbackMap_eq hp a a
  obtain ⟨vβ, hvβ, hβfac'⟩ := exists_comp_pullbackMap_eq hp a b
  let α : x ⟶ y := Functor.Fiber.homMk p (p.obj A) vα
  let β : x ⟶ y := Functor.Fiber.homMk p (p.obj A) vβ
  have hαfac : Functor.Fiber.fiberInclusion.map α ≫ cart = a := hαfac'
  have hβfac : Functor.Fiber.fiberInclusion.map β ≫ cart = b := hβfac'
  have hcomp : F.map (Functor.Fiber.fiberInclusion.map α) ≫ F.map cart =
      F.map (Functor.Fiber.fiberInclusion.map β) ≫ F.map cart :=
    ((F.map_comp _ cart).symm.trans (congrArg (fun k => F.map k) hαfac)).trans
      (hab.trans ((F.map_comp _ cart).symm.trans
        (congrArg (fun k => F.map k) hβfac)).symm)
  have hFcart : q.IsStronglyCartesian (q.map (F.map cart)) (F.map cart) :=
    hq.isStronglyCartesian (F.map cart)
  have hαq : q.IsHomLift (𝟙 (p.obj A)) (F.map (Functor.Fiber.fiberInclusion.map α)) :=
    Functor.isHomLift_map_of_comp_eq hF.comp_eq (𝟙 (p.obj A)) _
  have hβq : q.IsHomLift (𝟙 (p.obj A)) (F.map (Functor.Fiber.fiberInclusion.map β)) :=
    Functor.isHomLift_map_of_comp_eq hF.comp_eq (𝟙 (p.obj A)) _
  have hbaseαβ : q.map (F.map (Functor.Fiber.fiberInclusion.map α)) =
      q.map (F.map (Functor.Fiber.fiberInclusion.map β)) :=
    (IsHomLift.fac' q (𝟙 (p.obj A)) (F.map (Functor.Fiber.fiberInclusion.map α))).trans
      (IsHomLift.fac' q (𝟙 (p.obj A))
        (F.map (Functor.Fiber.fiberInclusion.map β))).symm
  have hβLift : q.IsHomLift (q.map (F.map (Functor.Fiber.fiberInclusion.map α)))
      (F.map (Functor.Fiber.fiberInclusion.map β)) :=
    Functor.isHomLift_of_eq (IsHomLift.map _) hbaseαβ.symm
  have hαβ : F.map (Functor.Fiber.fiberInclusion.map α) =
      F.map (Functor.Fiber.fiberInclusion.map β) :=
    Functor.IsStronglyCartesian.ext q (q.map (F.map cart)) (F.map cart)
      (q.map (F.map (Functor.Fiber.fiberInclusion.map α))) hcomp
  have hFiberαβ :
      (Functor.fiberFunctorOfCompEq hF.comp_eq (p.obj A)).map α =
        (Functor.fiberFunctorOfCompEq hF.comp_eq (p.obj A)).map β :=
    Functor.Fiber.hom_ext hαβ
  obtain ⟨R, hR, hloc⟩ :=
    CategoryTheory.exists_covering_eq hF J (heq.1 (p.obj A) x y).1 α β hFiberαβ
  refine (p.inheritedTopology J).superset_covering ?_
    (mem_inheritedTopology_functorPullback p J A hR)
  intro Z g hg
  change R.arrows (p.map g) at hg
  obtain ⟨v, -, hv⟩ := exists_comp_pullbackMap_eq hp g g
  have hkey : Functor.IsPreFibered.pullbackMap x.2 (p.map g) ≫
        Functor.Fiber.fiberInclusion.map α =
      Functor.IsPreFibered.pullbackMap x.2 (p.map g) ≫ Functor.Fiber.fiberInclusion.map β :=
    (Functor.pullbackFiberHom_fac α (p.map g)).symm.trans
      ((congrArg (fun m => Functor.Fiber.fiberInclusion.map m ≫
          Functor.IsPreFibered.pullbackMap y.2 (p.map g)) (hloc (p.map g) hg)).trans
        (Functor.pullbackFiberHom_fac β (p.map g)))
  change g ≫ a = g ≫ b
  exact CategoryTheory.comp_eq_comp_of_fac v _ hv cart hkey hαfac hβfac

/-- **Cover-dense.** A 1-morphism inducing an equivalence of stackifications is cover-dense for
the inherited topology of the target: every object of `𝒴` is covered by images of objects of
`𝒳`.

Clause (2) of Stacks 02ZN provides, over each member of a covering sieve of the base, an object
of `𝒳` whose image is isomorphic in the fibre to the chosen pullback; the composites of those
isomorphisms with the comparison maps of the chosen pullbacks form a covering family of
strongly cartesian morphisms, and they are images of `F` by construction. -/
theorem isCoverDense_of_isStackificationEquivalence (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence J) :
    F.IsCoverDense (q.inheritedTopology J) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨R, hR, hloc⟩ := heq.2 (q.obj y) (Functor.Fiber.mk rfl)
  let I := Σ V : C, {k : V ⟶ q.obj y // R.arrows k}
  let xx : ∀ z : I, p.Fiber z.1 := fun z => (hloc z.2.2).choose
  let ee : ∀ z : I,
      (Functor.fiberFunctorOfCompEq hF.comp_eq z.1).obj (xx z) ≅
        Functor.pullbackFiber q (Functor.Fiber.mk rfl) z.2.1 := fun z =>
    (hloc z.2.2).choose_spec.some
  let g : ∀ z : I, F.obj (xx z).1 ⟶ y := fun z =>
    Functor.Fiber.fiberInclusion.map (ee z).hom ≫
      Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk rfl).2 z.2.1
  have hbaseObj (z : I) : q.obj (F.obj (xx z).1) = z.1 := by
    rw [← Functor.comp_obj, hF.comp_eq]
    exact (xx z).2
  have h₁lift (z : I) : q.IsHomLift (𝟙 z.1)
      (Functor.Fiber.fiberInclusion.map (ee z).hom) := (ee z).hom.2
  have hmap (z : I) : q.map (g z) = eqToHom (hbaseObj z) ≫ z.2.1 :=
    Functor.map_comp_eq_eqToHom_comp q (Functor.Fiber.fiberInclusion.map (ee z).hom)
      (Functor.IsPreFibered.pullbackMap
        (Functor.Fiber.mk (rfl : q.obj y = q.obj y)).2 z.2.1) (h₁lift z)
      (inferInstanceAs (q.IsHomLift z.2.1 (Functor.IsPreFibered.pullbackMap
        (Functor.Fiber.mk (rfl : q.obj y = q.obj y)).2 z.2.1))) (hbaseObj z)
  have hbase : Sieve.ofArrows (fun z : I => q.obj (F.obj (xx z).1))
      (fun z => q.map (g z)) = R := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro V k ⟨z⟩
      rw [hmap z]
      exact R.downward_closed z.2.2 (eqToHom (hbaseObj z))
    · intro V k hk
      let z : I := ⟨V, ⟨k, hk⟩⟩
      have hz : (Sieve.ofArrows (fun z : I => q.obj (F.obj (xx z).1))
          (fun z => q.map (g z))).arrows (q.map (g z)) :=
        Sieve.ofArrows_mk _ _ z
      rw [hmap z] at hz
      simpa [z] using (Sieve.ofArrows (fun z : I => q.obj (F.obj (xx z).1))
        (fun z => q.map (g z))).downward_closed hz (eqToHom (hbaseObj z).symm)
  have hgen := generate_ofArrows_mem_inheritedTopology q J g (fun z => hq.isStronglyCartesian (g z))
    (by rwa [hbase])
  refine (q.inheritedTopology J).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro z
  exact Presieve.in_coverByImage F (g z)

/-- A 1-morphism of categories fibred in groupoids inducing an equivalence of stackifications is
a dense subsite inclusion for the inherited topologies of Stacks 06NV: it is cover-dense,
locally full and locally faithful. -/
theorem isDenseSubsite_of_isStackificationEquivalence [HasPullbacks C]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence J) :
    F.IsDenseSubsite (p.inheritedTopology J) (q.inheritedTopology J) := by
  let : F.IsContinuous (p.inheritedTopology J) (q.inheritedTopology J) :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology J).1
  let : F.IsCocontinuous (p.inheritedTopology J) (q.inheritedTopology J) :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology J).2
  let : F.IsCoverDense (q.inheritedTopology J) :=
    isCoverDense_of_isStackificationEquivalence J hq hF heq
  exact Functor.isDenseSubsite_of_isCocontinuous F (p.inheritedTopology J)
    (q.inheritedTopology J)
    (CoverPreserving.of_isContinuous F (p.inheritedTopology J) (q.inheritedTopology J))
    (fun _ _ a b hab => equalizerSieve_mem_inheritedTopology J hp hq hF heq a b hab)
    (fun _ _ c => imageSieve_mem_inheritedTopology J hp hF heq c)

end IsFibredOneMorphism

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

/-- If a 1-morphism `F : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over the big fppf category of
`S` satisfies the two local clauses of Stacks 02ZN
(`CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence`), then the morphism of
topoi `Sh(𝒳_fppf) ⟶ Sh(𝒴_fppf)` of Stacks 06TS is an equivalence. Stacks 06WQ, whose hypothesis
is that `F` induces an equivalence of stackifications, is derived from this as
`AlgebraicGeometry.Stack.isEquivalence_inverseImage_of_isEquivalenceOver_stackifications`.

The functor displayed is the inverse image of that morphism of topoi, which by Stacks 06TS is
restriction along `F`; the morphism of topoi is an equivalence exactly when its inverse image
is. -/
theorem isEquivalence_inverseImage_of_isStackificationEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v₁} [Category.{u} 𝒳] {𝒴 : Type v₂} [Category.{u} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q F)
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence (BigFppfOver.topology B S hS)) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      (BigFppfOver.topology B S hS)).1
    (F.sheafPushforwardContinuous (Type (max t u v₁ v₂))
      (p.inheritedTopology (BigFppfOver.topology B S hS))
      (q.inheritedTopology (BigFppfOver.topology B S hS))).IsEquivalence := by
  let J₀ := BigFppfOver.topology B S hS
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let : F.IsContinuous (p.inheritedTopology J₀) (q.inheritedTopology J₀) :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology J₀).1
  let : F.IsDenseSubsite (p.inheritedTopology J₀) (q.inheritedTopology J₀) :=
    Functor.IsFibredOneMorphism.isDenseSubsite_of_isStackificationEquivalence J₀ hp hq hF heq
  infer_instance

end AlgebraicGeometry.Stack

end
