module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Stackification
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Additions to `Stackification`

Declarations this development adds alongside
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Stackification`, kept in their own module so that the
base file is unchanged: 6 declaration(s) that the base file does not have, with the section
variables, namespaces and options they are stated in.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u uC v₁ v₂ w t

namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{w} C] {X : Type v₁} [Category.{w} X]
  {Y : Type v₂} [Category.{w} Y]

end CategoryTheory.Functor

/-! ### The morphisms of the base in an independent universe

The unprimed statements after this block take the morphisms of the base site in the universe of
the morphisms of the two fibred categories. Nothing in the arguments needs that: the morphism
presheaves of Stacks 02ZN tie together only the hom universes of the source and of the target. The
primed declarations below are the same statements with the hom universe `wC` of the base free,
which is the shape of a category fibred in groupoids whose morphisms live in a larger universe than
those of the base, such as the quotient stack of a groupoid in algebraic spaces. The unprimed
statements are derived from them. -/

namespace CategoryTheory.Functor

universe wC

variable {C : Type uC} [Category.{wC} C] {X : Type v₁} [Category.{w} X]
  {Y : Type v₂} [Category.{w} Y]

/-- A family of strongly cartesian arrows to `a` whose images generate a covering sieve of the base
generates a covering sieve for the inherited topology. -/
private theorem generate_ofArrows_mem_inheritedTopology {C : Type uC} [Category.{wC} C]
    {X : Type v₁} [Category.{w} X] (r : X ⥤ C) [r.IsFibered] (J : GrothendieckTopology C) (a : X)
    {I : Type*} (Z : I → X) (g : ∀ i, Z i ⟶ a)
    (hg : ∀ i, r.IsStronglyCartesian (r.map (g i)) (g i))
    (h : Sieve.ofArrows (fun i => r.obj (Z i)) (fun i => r.map (g i)) ∈ J (r.obj a)) :
    Sieve.generate (Presieve.ofArrows Z g) ∈ r.inheritedTopology J a := by
  have hmem : Presieve.ofArrows Z g ∈ r.inheritedPrecoverage J.toPrecoverage a := by
    refine ⟨fun _ _ hz => ?_, ?_⟩
    · obtain ⟨i⟩ := hz
      exact hg i
    · rwa [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
  rw [Functor.inheritedTopology_eq]
  exact Precoverage.generate_mem_toGrothendieck hmem

/-- A covering sieve of the base pulls back, along a fibred functor, to a covering sieve for the
inherited topology of Stacks 06NV: its strongly cartesian lifts form an inherited covering
family, and each of them is in the pullback. -/
theorem mem_inheritedTopology_functorPullback'
    {C : Type uC} [Category.{wC} C] {X : Type v₁} [Category.{w} X] (r : X ⥤ C) [r.IsFibered]
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
    (generate_ofArrows_mem_inheritedTopology r J a Z g (fun i => i.2.2.1) (by rwa [himg]))
  rw [Sieve.generate_le_iff]
  rintro V k ⟨i⟩
  exact i.2.2.2

namespace IsFibredOneMorphism

variable {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered] {F : X ⥤ Y}

/-- A 1-morphism `F` of categories fibred in groupoids over a site *induces an equivalence of
stackifications* when it satisfies the two local criteria of Stacks 02ZN: on every fibre the
induced map of morphism presheaves is locally injective and locally surjective, and every object
of a fibre of the target is, along a covering sieve of the base, in the essential image of `F`
on fibres.

These are the conditions characterizing a stackification, so they hold for `F` exactly when the
stackifications of source and target are equivalent over `F`; stating the hypothesis in this
form avoids constructing either stackification. The second clause is
`CategoryTheory.Functor.LocallyEssSurjOnFibers`, spelled with
`CategoryTheory.Functor.fiberFunctorOfCompEq` rather than
`CategoryTheory.Functor.Fiber.mapOfComp` because that is the spelling the criteria of
Stacks 04WR are stated in. -/
def IsStackificationEquivalence'
    {C : Type uC} [Category.{wC} C] {X : Type v₁} [Category.{w} X]
    {Y : Type v₂} [Category.{w} Y]
    {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered] {F : X ⥤ Y}
    (hF : p.IsFibredOneMorphism q F)
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
theorem imageSieve_mem_inheritedTopology' [HasPullbacks C] (hp : p.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence' J)
    ⦃A Bb : X⦄ (c : F.obj A ⟶ F.obj Bb) :
    F.imageSieve c ∈ p.inheritedTopology J A := by
  obtain ⟨R, hR, hlift⟩ := CategoryTheory.exists_covering_lift_hom_of_baseHomUniverse hF J heq.1 c
  refine (p.inheritedTopology J).superset_covering ?_
    (mem_inheritedTopology_functorPullback' p J A hR)
  intro Z g hg
  change R.arrows (p.map g) at hg
  obtain ⟨wlift, hw⟩ := hlift (p.map g) hg
  have hone : p.map g = 𝟙 _ ≫ p.map g := by simp
  let cart := Functor.IsPreFibered.pullbackMap (rfl : p.obj A = p.obj A) (p.map g)
  have hcart : p.IsStronglyCartesian (p.map g) cart :=
    hp.isStronglyCartesian_homLift (p.map g) cart
  let v := Functor.IsStronglyCartesian.map p (p.map g) cart hone g
  have hv : v ≫ cart = g := Functor.IsStronglyCartesian.fac p (p.map g) cart hone g
  refine ⟨v ≫ wlift, ?_⟩
  have e1 : F.map (v ≫ wlift) = F.map v ≫ F.map wlift := F.map_comp v wlift
  have e2 : F.map v ≫ F.map wlift = F.map v ≫ F.map cart ≫ c :=
    congrArg (fun k => F.map v ≫ k) hw.symm
  have e3 : F.map v ≫ F.map cart ≫ c = F.map (v ≫ cart) ≫ c :=
    (Category.assoc (F.map v) (F.map cart) c).symm.trans
      (congrArg (fun k => k ≫ c) (F.map_comp v cart).symm)
  have e4 : F.map (v ≫ cart) ≫ c = F.map g ≫ c :=
    congrArg (fun k => F.map k ≫ c) hv
  exact e1.trans (e2.trans (e3.trans e4))

/-- **Locally faithful.** A 1-morphism inducing an equivalence of stackifications is locally
faithful for the inherited topologies: two parallel arrows of `𝒳` with the same image agree
along a covering sieve.

The two arrows lie over one and the same arrow `f` of the base, because `F` commutes with the
structure functors and is injective on the base by fibredness of the target; so each of them is
the comparison map of a chosen cartesian lift of `f` composed with an arrow of a fibre, and the
injectivity half of clause (1) of Stacks 02ZN applies to those two arrows of the fibre. -/
theorem equalizerSieve_mem_inheritedTopology' (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (hF : p.IsFibredOneMorphism q F)
    (heq : hF.IsStackificationEquivalence' J)
    {A Bb : X} (a b : A ⟶ Bb) (hab : F.map a = F.map b) :
    Sieve.equalizer a b ∈ p.inheritedTopology J A := by
  have hf : p.map b = p.map a := by
    rw [Functor.map_eq_of_comp_eq p q F hF.comp_eq a,
      Functor.map_eq_of_comp_eq p q F hF.comp_eq b, hab]
  have hbLift : p.IsHomLift (p.map a) b := Functor.isHomLift_of_eq (IsHomLift.map b) hf
  have hone : p.map a = 𝟙 (p.obj A) ≫ p.map a := by simp
  let x : p.Fiber (p.obj A) := Functor.Fiber.mk rfl
  let y : p.Fiber (p.obj A) := Functor.Fiber.mk
    (Functor.IsPreFibered.pullbackObj_proj (rfl : p.obj Bb = p.obj Bb) (p.map a))
  let cart : Functor.Fiber.fiberInclusion.obj y ⟶ Bb :=
    Functor.IsPreFibered.pullbackMap (rfl : p.obj Bb = p.obj Bb) (p.map a)
  have hcartLift : p.IsHomLift (p.map a) cart :=
    inferInstanceAs (p.IsHomLift (p.map a)
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj Bb = p.obj Bb) (p.map a)))
  have hcart : p.IsStronglyCartesian (p.map a) cart :=
    hp.isStronglyCartesian_homLift (p.map a) cart
  let α : x ⟶ y := Functor.Fiber.homMk p (p.obj A)
    (Functor.IsStronglyCartesian.map p (p.map a) cart hone a)
  let β : x ⟶ y := Functor.Fiber.homMk p (p.obj A)
    (Functor.IsStronglyCartesian.map p (p.map a) cart hone b)
  have hαfac : Functor.Fiber.fiberInclusion.map α ≫ cart = a :=
    Functor.IsStronglyCartesian.fac p (p.map a) cart hone a
  have hβfac : Functor.Fiber.fiberInclusion.map β ≫ cart = b :=
    Functor.IsStronglyCartesian.fac p (p.map a) cart hone b
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
    CategoryTheory.exists_covering_eq_of_baseHomUniverse hF J
      (heq.1 (p.obj A) x y).1 α β hFiberαβ
  refine (p.inheritedTopology J).superset_covering ?_
    (mem_inheritedTopology_functorPullback' p J A hR)
  intro Z g hg
  change R.arrows (p.map g) at hg
  have hone' : p.map g = 𝟙 (p.obj Z) ≫ p.map g := by simp
  let pm : Functor.IsPreFibered.pullbackObj x.2 (p.map g) ⟶ A :=
    Functor.IsPreFibered.pullbackMap x.2 (p.map g)
  have hpm : p.IsStronglyCartesian (p.map g) pm :=
    inferInstanceAs (p.IsStronglyCartesian (p.map g)
      (Functor.IsPreFibered.pullbackMap x.2 (p.map g)))
  let v := Functor.IsStronglyCartesian.map p (p.map g) pm hone' g
  have hv : v ≫ pm = g := Functor.IsStronglyCartesian.fac p (p.map g) pm hone' g
  have hkey : pm ≫ Functor.Fiber.fiberInclusion.map α =
      pm ≫ Functor.Fiber.fiberInclusion.map β :=
    (Functor.pullbackFiberHom_fac α (p.map g)).symm.trans
      ((congrArg (fun m => Functor.Fiber.fiberInclusion.map m ≫
          Functor.IsPreFibered.pullbackMap y.2 (p.map g)) (hloc (p.map g) hg)).trans
        (Functor.pullbackFiberHom_fac β (p.map g)))
  show g ≫ a = g ≫ b
  exact CategoryTheory.comp_eq_comp_of_fac v pm hv cart hkey hαfac hβfac

/-- **Cover-dense.** A 1-morphism inducing an equivalence of stackifications is cover-dense for
the inherited topology of the target: every object of `𝒴` is covered by images of objects of
`𝒳`.

Clause (2) of Stacks 02ZN provides, over each member of a covering sieve of the base, an object
of `𝒳` whose image is isomorphic in the fibre to the chosen pullback; the composites of those
isomorphisms with the comparison maps of the chosen pullbacks form a covering family of
strongly cartesian morphisms, and they are images of `F` by construction. -/
theorem isCoverDense_of_isStackificationEquivalence' (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence' J) :
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
      have hdc := (Sieve.ofArrows (fun z : I => q.obj (F.obj (xx z).1))
          (fun z => q.map (g z))).downward_closed hz (eqToHom (hbaseObj z).symm)
      simpa [z] using hdc
  have hgen := generate_ofArrows_mem_inheritedTopology q J y (fun z : I => F.obj (xx z).1) g
    (fun z => hq.isStronglyCartesian (g z)) (by rwa [hbase])
  refine (q.inheritedTopology J).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun z => Presieve.in_coverByImage F (g z)

/-- A 1-morphism of categories fibred in groupoids inducing an equivalence of stackifications is
a dense subsite inclusion for the inherited topologies of Stacks 06NV: it is cover-dense,
locally full and locally faithful. -/
theorem isDenseSubsite_of_isStackificationEquivalence' [HasPullbacks C]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) (heq : hF.IsStackificationEquivalence' J) :
    F.IsDenseSubsite (p.inheritedTopology J) (q.inheritedTopology J) := by
  have : F.IsContinuous (p.inheritedTopology J) (q.inheritedTopology J) :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology J).1
  have : F.IsCocontinuous (p.inheritedTopology J) (q.inheritedTopology J) :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology J).2
  have : F.IsCoverDense (q.inheritedTopology J) :=
    isCoverDense_of_isStackificationEquivalence' J hq hF heq
  exact Functor.isDenseSubsite_of_isCocontinuous F (p.inheritedTopology J)
    (q.inheritedTopology J)
    (CoverPreserving.of_isContinuous F (p.inheritedTopology J) (q.inheritedTopology J))
    (fun _ _ => equalizerSieve_mem_inheritedTopology' J hp hq hF heq)
    (imageSieve_mem_inheritedTopology' J hp hF heq)

end IsFibredOneMorphism

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{w} C] {X : Type v₁} [Category.{w} X]
  {Y : Type v₂} [Category.{w} Y]

namespace IsFibredOneMorphism

variable {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered] {F : X ⥤ Y}

variable (J : GrothendieckTopology C)

end IsFibredOneMorphism

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

end AlgebraicGeometry.Stack

end
