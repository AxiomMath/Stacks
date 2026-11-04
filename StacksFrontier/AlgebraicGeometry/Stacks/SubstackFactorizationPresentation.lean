module

public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.LocallyClosedSieve
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EssentiallySurjective

/-!
# Factorization through a substack is checked on a presentation (Stacks 0507)

Let `𝒳` be an algebraic stack over `S` with a presentation `[U/R] ≅ 𝒳` by a smooth groupoid
in algebraic spaces, let `P` cut out an open, closed or locally closed substack of `𝒳`, and let
`f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks. The second assertion of Stacks 0507 is that
`f` factors through the substack if and only if its base change along the presentation
`S_U ⟶ 𝒳` factors through the base change of the substack.

## Main results

* `AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation`: **Stacks 0507**, the
  factorization criterion.
* `AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation_of_isAlgebraicStack`: the
  factorization criterion for any property closed under isomorphism whose full subcategory is an
  algebraic stack. The three bijections of Stacks 0507, each with this criterion, are registered in
  `StacksFrontier.AlgebraicGeometry.Stacks.SubstackPresentationCorrespondence`.

## Implementation notes

Both sides of the criterion are existential statements about a 1-morphism over the big fppf
site together with a 2-isomorphism to the given one, and both are *pointwise*: because the
inclusion of a full subcategory is fully faithful and the substack property is closed under
isomorphism, a factorization exists exactly when the property holds at every object in the
image. That is `AlgebraicGeometry.Stack.exists_based_factorization_iff` on the left and
`CategoryTheory.TwoFibreProductOver.exists_based_factorization_fst_iff` on the right, and
neither needs any geometry: the second is proved by lifting the 2-fibre product objectwise,
`CategoryTheory.TwoFibreProductOver.liftFullSubcategory`.

What the criterion then amounts to is that membership of the substack is *local* on the big
fppf site, together with the fact that the presentation is locally essentially surjective. The
first is `AlgebraicGeometry.Stack.prop_of_locally_isoOverId`, which is the converse direction of
condition (3) of Stacks 04TU: it is read off from
`CategoryTheory.Functor.exists_iso_of_locally_essImage`, whose hypotheses — effective descent
for the substack and the `Mor`-sheaf condition for `𝒳` — are exactly the clauses of Stacks 026F
that `AlgebraicGeometry.Stack.isStack_of_isAlgebraicStack` supplies for the two algebraic
stacks. The second is `AlgebraicGeometry.Stack.exists_local_hom_from_presentation`, which
transports part (1) of Stacks 044X from the quotient stack to `𝒳` along the comparison
equivalence, using the quasi-inverse *over the base* of Stacks 003Z so that the comparison
isomorphism it produces is vertical.

Smoothness of the groupoid is not used: part (1) of Stacks 044X holds for the quotient stack of
any groupoid in algebraic spaces, because the quotient is by construction the stackification of
the pointwise groupoid fibration. It is carried as a hypothesis because the source states the
criterion for a presentation.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {Xx : Type u₂} [Category.{v₂} Xx]
  {Yy : Type u₄} [Category.{v₄} Yy] {𝒰 : BasedCategory.{v₃, u₃} 𝒞}

variable {p𝒴 : Yy ⥤ 𝒞} {p𝒳 : Xx ⥤ 𝒞} {a : 𝒰.obj ⥤ Xx} {b : Yy ⥤ Xx}

/-- The lift of the 2-fibre product `𝒰 ×_𝒳 𝒴` to the 2-fibre product of `𝒰` with the full
subcategory of `𝒳` cut out by `P`, available when `P` holds at every object in the image of the
`𝒴`-leg. It is the identity on the base object, on the `𝒰`-component and on the comparison
isomorphism; only the `𝒴`-component moves, to the image of the `𝒴`-leg tagged with its
membership proof. -/
def TwoFibreProductOver.liftFullSubcategory (hb : b ⋙ p𝒳 = p𝒴) (P : ObjectProperty Xx)
    (h : ∀ d : TwoFibreProductOver 𝒰.p p𝒴 p𝒳 a b, P (b.obj d.y)) :
    TwoFibreProductOver 𝒰.p p𝒴 p𝒳 a b ⥤
      TwoFibreProductOver 𝒰.p (P.ι ⋙ p𝒳) p𝒳 a P.ι where
  obj d :=
    { base := d.base
      x := d.x
      y := ⟨b.obj d.y, h d⟩
      hx := d.hx
      hy := (Functor.congr_obj hb d.y).trans d.hy
      iso := d.iso
      vertical := d.vertical }
  map {d d'} φ :=
    { hbase := φ.hbase
      a := φ.a
      b := ObjectProperty.homMk (b.map φ.b)
      ha := φ.ha
      hb := by
        rw [Functor.isHomLift_comp_iff, ObjectProperty.ι_map, ObjectProperty.homMk_hom]
        have := φ.hb
        exact Functor.isHomLift_map_of_comp_eq hb φ.hbase φ.b
      w := φ.w }
  map_id d := TwoFibreProductOver.Hom.ext' rfl (ObjectProperty.hom_ext P (by simp))
  map_comp φ ψ := TwoFibreProductOver.Hom.ext' rfl (ObjectProperty.hom_ext P (by simp))

/-- The first projection of a 2-fibre product over `𝒰`, as a 1-morphism over the base. -/
abbrev TwoFibreProductOver.fstBased (p𝒴 : Yy ⥤ 𝒞) (p𝒳 : Xx ⥤ 𝒞) (a : 𝒰.obj ⥤ Xx)
    (b : Yy ⥤ Xx) :
    BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor 𝒰.p p𝒴 p𝒳 a b) ⥤ᵇ 𝒰 where
  toFunctor := TwoFibreProductOver.fst 𝒰.p p𝒴 p𝒳 a b
  w := TwoFibreProductOver.fst_comp_eq

/-- A factorization of the first projection of `𝒰 ×_𝒳 𝒴` through the first projection of the
2-fibre product of `𝒰` with the full subcategory cut out by `P`, over the base and up to a
2-isomorphism, exists exactly when `P` holds at every object in the image of the `𝒴`-leg.

One direction tags the `𝒴`-leg with its membership proof, which is
`CategoryTheory.TwoFibreProductOver.liftFullSubcategory` and makes the composite equal to the
projection on the nose. The other reads `P` off the `𝒴`-component of the factorization, using
that the comparison isomorphisms of the two 2-fibre products and the 2-isomorphism of the
factorization compose to an isomorphism in `𝒳`. -/
theorem TwoFibreProductOver.exists_based_factorization_fst_iff (hb : b ⋙ p𝒳 = p𝒴)
    (P : ObjectProperty Xx) [P.IsClosedUnderIsomorphisms] :
    (∃ g : BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor 𝒰.p p𝒴 p𝒳 a b) ⥤ᵇ
        BasedCategory.ofFunctor
          (TwoFibreProductOver.structureFunctor 𝒰.p (P.ι ⋙ p𝒳) p𝒳 a P.ι),
      Nonempty (g.comp (TwoFibreProductOver.fstBased (P.ι ⋙ p𝒳) p𝒳 a P.ι) ≅
        TwoFibreProductOver.fstBased p𝒴 p𝒳 a b)) ↔
      ∀ d : TwoFibreProductOver 𝒰.p p𝒴 p𝒳 a b, P (b.obj d.y) := by
  refine ⟨fun ⟨g, ⟨α⟩⟩ d => P.prop_of_iso
    ((g.obj d).iso.symm.trans
      ((a.mapIso (((BasedNatTrans.forgetful _ _).mapIso α).app d)).trans d.iso))
    (g.obj d).y.property, fun h => ?_⟩
  exact ⟨⟨TwoFibreProductOver.liftFullSubcategory hb P h, rfl⟩, ⟨BasedNatIso.id _⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Each of the three substack conditions of Stacks 04YM supplies strict fullness of the
object property and algebraicity of the full subcategory it cuts out, and those are the only
two consequences the factorization criterion uses. -/
theorem isClosedUnderIsomorphisms_and_isAlgebraicStack_of_substack
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
    (hP : (IsLocallyClosedSubstack 𝒳 P ∨ IsClosedSubstack 𝒳 P) ∨
      ∃ V : OpenSubstack 𝒳, V.property = P) :
    P.IsClosedUnderIsomorphisms ∧
      IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) := by
  rcases hP with (⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩) | ⟨V, rfl⟩
  exacts [⟨h₁, h₂⟩, ⟨h₁, h₂⟩, ⟨V.strictlyFull, V.isAlgebraic⟩]

/-- A 1-morphism into an algebraic stack factors through the full subcategory cut out by a
property closed under isomorphism, over the base and up to a 2-isomorphism, exactly when the
property holds at every object in its image.

One direction tags each object of the image with its membership proof, which makes the
composite with the inclusion equal to the original 1-morphism on the nose; the other reads the
property off the 2-isomorphism, using that it is closed under isomorphism. -/
theorem exists_based_factorization_iff
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
    [P.IsClosedUnderIsomorphisms] {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ g : 𝒟 ⥤ᵇ fullSubcategoryBased 𝒳 P,
        Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P) ≅ f)) ↔
      ∀ Y : 𝒟.obj, P (f.obj Y) := by
  refine ⟨fun ⟨g, ⟨α⟩⟩ Y =>
    P.prop_of_iso (((BasedNatTrans.forgetful _ _).mapIso α).app Y) (g.obj Y).property,
    fun h => ⟨⟨P.lift f.toFunctor h, f.w⟩, ⟨BasedNatIso.id _⟩⟩⟩

/-- Membership of a substack is local on the big fppf site: if the chosen pullbacks of an object
of a fibre of `𝒳` along the members of a covering sieve are isomorphic over the identity to
objects of the substack, then so is the object itself, hence — the substack being strictly
full — it lies in the substack.

This is the converse direction of condition (3) of Stacks 04TU, and it is
`CategoryTheory.Functor.exists_iso_of_locally_essImage` for the fully faithful inclusion of the
full subcategory: effective descent for the substack and the `Mor`-sheaf condition for `𝒳` are
the clauses of Stacks 026F that `AlgebraicGeometry.Stack.isStack_of_isAlgebraicStack` supplies
for the two algebraic stacks. -/
theorem prop_of_locally_isoOverId
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
    [P.IsClosedUnderIsomorphisms] [𝒳.val.val.p.IsFibered]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {V : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber V)
    {R : Sieve V} (hR : R ∈ BigFppfOver.topology B S hS V)
    (hloc : ∀ ⦃V' : BigFppfOver B S hS⦄ (k : V' ⟶ V), R.arrows k →
      Functor.IsoOverId 𝒳.val.val.p P (Functor.pullbackFiber 𝒳.val.val.p x k).1) :
    P x.1 := by
  have hstX : 𝒳.val.val.p.IsStack (BigFppfOver.topology B S hS) :=
    isStack_of_isAlgebraicStack B S hS 𝒳.property
  have hstP : (fullSubcategoryBased 𝒳 P).p.IsStack (BigFppfOver.topology B S hS) :=
    isStack_of_isAlgebraicStack B S hS hPalg
  have hfibP : (Functor.restrict 𝒳.val.val.p P).IsFibered := hstP.isFibered
  have hF : Functor.IsFibredOneMorphism (Functor.restrict 𝒳.val.val.p P) 𝒳.val.val.p P.ι :=
    Functor.IsFiberedInGroupoids.isFibredOneMorphism 𝒳.val.property rfl
  obtain ⟨x₁, ⟨e⟩⟩ := Functor.exists_iso_of_locally_essImage hF hstP.hasEffectiveDescent
    (hstX.isMorSheaf V) x hR (fun {V'} k hk => by
      obtain ⟨y', hy', ey, hey⟩ := hloc k hk
      have hpb : 𝒳.val.val.p.obj (Functor.pullbackFiber 𝒳.val.val.p x k).1 = V' :=
        (Functor.pullbackFiber 𝒳.val.val.p x k).2
      have hy'o : (Functor.restrict 𝒳.val.val.p P).obj ⟨y', hy'⟩ = V' :=
        (IsHomLift.codomain_eq 𝒳.val.val.p
          (𝟙 (𝒳.val.val.p.obj (Functor.pullbackFiber 𝒳.val.val.p x k).1)) ey.hom).trans hpb
      refine ⟨⟨⟨y', hy'⟩, hy'o⟩, ⟨Functor.Fiber.isoMk ey.symm ?_⟩⟩
      have hinv : 𝒳.val.val.p.IsHomLift
          (𝟙 (𝒳.val.val.p.obj (Functor.pullbackFiber 𝒳.val.val.p x k).1)) ey.symm.hom := by
        simpa using IsHomLift.inv 𝒳.val.val.p
          (𝟙 (𝒳.val.val.p.obj (Functor.pullbackFiber 𝒳.val.val.p x k).1)) ey.hom
      rwa [hpb] at hinv)
  exact P.prop_of_iso ((Functor.Fiber.fiberInclusion (p := 𝒳.val.val.p)).mapIso e) x₁.1.property

/-- The composite of two 1-morphisms over the base acts on objects as the composite of the two
functors. -/
theorem basedComp_obj {𝒞 : Type (u + 1)} [Category.{u} 𝒞]
    {𝒜 ℬ 𝒟 : BasedCategory.{u, u + 1} 𝒞} (F : 𝒜 ⥤ᵇ ℬ) (K : ℬ ⥤ᵇ 𝒟) (a : 𝒜.obj) :
    (F.comp K).obj a = K.obj (F.obj a) := rfl

/-- The projection of Stacks 044R, read through the universe lift of the object space that
`AlgebraicGeometry.Stack.quotientStackProjectionHom` is built from. -/
theorem homFunctor_quotientStackProjectionHom_obj
    {Bs : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (z : (liftedObjectSpace G).val.obj) :
    (CatFiberedInGroupoids.homFunctor (quotientStackProjectionHom G)).obj z
      = (quotientStackProjection G).obj ((objectSpaceLiftDown G).obj z) := rfl

/-- **Part (1) of Stacks 044X along a presentation.** Every object of a fibre of a presented
algebraic stack receives, over the members of some fppf covering sieve, a morphism from the
image under the presentation of an object of the presenting object space.

The quasi-inverse of the comparison equivalence is taken *over the base*, by Stacks 003Z, so
that the counit component at the object is vertical; composing it with the local morphism
supplied by `AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom` leaves a morphism
over the same arrow of the site. No hypothesis on the groupoid is needed. -/
theorem exists_local_hom_from_presentation
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
    (E : (quotientStack G).obj ⥤ 𝒳.val.val.obj) [E.IsEquivalence]
    (hE : E ⋙ 𝒳.val.val.p = (quotientStack G).p)
    (V : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber V) :
    ∃ R ∈ BigFppfOver.topology B S hS V,
      ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃k : V' ⟶ V⦄, R.arrows k →
        ∃ (uu : (fibredCategory B S hS G.objects.obj).val.obj)
          (ζ : E.obj ((quotientStackProjection G).obj uu) ⟶ x.1),
          𝒳.val.val.p.IsHomLift k ζ := by
  obtain ⟨Fi, hFi, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (quotientStack G).p 𝒳.val.val.p (isFiberedInGroupoids_quotientStack G) 𝒳.val.property
    E hE inferInstance
  obtain ⟨xo, rfl⟩ := x
  have hxt : (quotientStack G).p.obj (Fi.obj xo) = 𝒳.val.val.p.obj xo := by
    rw [← Functor.comp_obj, hFi]
  obtain ⟨R, hR, hloc⟩ :=
    localEssSurj_quotientStackProjectionHom G (𝒳.val.val.p.obj xo) ⟨Fi.obj xo, hxt⟩
  refine ⟨R, hR, fun V' k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := hloc hk
  refine ⟨(objectSpaceLiftDown G).obj z, E.map φ ≫ ε.hom.app xo, ?_⟩
  have h₁ : 𝒳.val.val.p.IsHomLift k (E.map φ) := Functor.isHomLift_map_of_comp_eq hE k φ
  have h₂ := hε xo
  simpa only [homFunctor_quotientStackProjectionHom_obj, Functor.id_obj, Category.comp_id] using
    IsHomLift.comp 𝒳.val.val.p k (𝟙 (𝒳.val.val.p.obj xo)) (E.map φ) (ε.hom.app xo)

/-- **The descent step of Stacks 0507.** If a substack property holds at the `𝒴`-leg of every
object of the 2-fibre product of the presenting object space with `𝒴` over `𝒳`, then it holds
at every object in the image of `𝒴`.

For an object `Y` of `𝒴` over `V`, the presentation supplies a covering sieve of `V` and, over
each of its members `k`, an object `u` of the object space with a morphism to `f Y` over `k`;
the chosen pullback of `Y` along `k` supplies another one. Both are strongly cartesian, because
`𝒳` is fibred in groupoids, so their domains are canonically isomorphic over the identity, which
is exactly the datum making `u` and that pullback an object of the 2-fibre product. The
hypothesis then gives the property at the chosen pullback of `f Y` along `k`, and
`AlgebraicGeometry.Stack.prop_of_locally_isoOverId` descends it to `f Y`. -/
theorem forall_prop_of_forall_twoFibreProduct
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
    (E : (quotientStack G).obj ⥤ 𝒳.val.val.obj) [E.IsEquivalence]
    (hE : E ⋙ 𝒳.val.val.p = (quotientStack G).p)
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (fb : 𝒴.val.val ⥤ᵇ 𝒳.val.val)
    (h : ∀ d : TwoFibreProductOver (fibredCategory B S hS G.objects.obj).val.p
          𝒴.val.val.p 𝒳.val.val.p
          ((quotientStackProjection G).comp
            (⟨E, hE⟩ : (quotientStack G) ⥤ᵇ 𝒳.val.val)).toFunctor fb.toFunctor,
        P (fb.obj d.y)) :
    ∀ Y : 𝒴.val.val.obj, P (fb.obj Y) := by
  have hfibX : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
  have hfibY : 𝒴.val.val.p.IsFibered := 𝒴.val.property.isFibered
  intro Y
  obtain ⟨R, hR, hlocpres⟩ := exists_local_hom_from_presentation G E hE
    (𝒴.val.val.p.obj Y) ⟨fb.obj Y, fb.w_obj Y⟩
  refine prop_of_locally_isoOverId hPalg ⟨fb.obj Y, fb.w_obj Y⟩ hR ?_
  intro V' k hk
  obtain ⟨uu, ζ, hζ⟩ := hlocpres hk
  set Yf : 𝒴.val.val.p.Fiber (𝒴.val.val.p.obj Y) := ⟨Y, rfl⟩
  set cY := Functor.IsPreFibered.pullbackMap Yf.2 k
  set ζY := fb.map cY
  have hcart {a b : 𝒳.val.val.obj} (φ : a ⟶ b) [𝒳.val.val.p.IsHomLift k φ] :
      𝒳.val.val.p.IsCartesian k φ := by
    have := 𝒳.val.property.isStronglyCartesian_homLift k φ
    exact inferInstance
  have hcζ := hcart ζ
  have hcζY := hcart ζY
  have hdomζ : 𝒳.val.val.p.obj (E.obj ((quotientStackProjection G).obj uu)) = V' :=
    IsHomLift.domain_eq 𝒳.val.val.p k ζ
  have hvert : 𝒳.val.val.p.IsHomLift (𝟙 V')
      (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p k ζY ζ).hom := inferInstance
  have hd : P (fb.obj (Functor.pullbackFiber 𝒴.val.val.p Yf k).1) :=
    h { base := V'
        x := uu
        y := (Functor.pullbackFiber 𝒴.val.val.p Yf k).1
        hx := (((quotientStackProjection G).comp
          (⟨E, hE⟩ : (quotientStack G) ⥤ᵇ 𝒳.val.val)).w_obj uu).symm.trans hdomζ
        hy := (Functor.pullbackFiber 𝒴.val.val.p Yf k).2
        iso := (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p k ζY ζ :
          E.obj ((quotientStackProjection G).obj uu) ≅
            fb.obj (Functor.pullbackFiber 𝒴.val.val.p Yf k).1)
        vertical := hvert }
  exact Functor.isoOverId_pullbackFiber 𝒳.val.val.p P ⟨fb.obj Y, fb.w_obj Y⟩ k ζY hcζY hd

/-- The factorization criterion of Stacks 0507 for any property `P` of the objects of `𝒳`
which is closed under isomorphism and whose full subcategory is an algebraic stack (as it is for
an open, closed or locally closed substack of `𝒳`). Let `𝒳` be an algebraic stack over `S`
presented by a smooth groupoid in algebraic spaces `G` through an equivalence `E` over the big
fppf site, and let `f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks. Then `f` factors through the
full subcategory cut out by `P`, over the big fppf site and up to a 2-isomorphism, if and only if
the base change of `f` along the presentation `S_U ⟶ 𝒳` factors through the base change of that
full subcategory.

The proof is pointwise on both sides, and the content is that membership of the substack is
local on the site; see the module documentation. -/
theorem factorsThroughSubstack_iff_presentation_of_isAlgebraicStack
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS)
    (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
    (_hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (E : (quotientStack G).obj ⥤ 𝒳.val.val.obj)
    [E.IsEquivalence]
    (hE : E ⋙ 𝒳.val.val.p = (quotientStack G).p)
    (P : ObjectProperty 𝒳.val.val.obj) [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (f : 𝒴 ⟶ 𝒳) :
    let U := (fibredCategory B S hS G.objects.obj).val
    let p := (quotientStackProjection G).comp
      (⟨E, hE⟩ : (quotientStack G) ⥤ᵇ 𝒳.val.val)
    let F := TwoFibreProductOver.structureFunctor U.p 𝒴.val.val.p 𝒳.val.val.p
      p.toFunctor f.hom.hom.toFunctor
    let D := BasedCategory.ofFunctor F
    let q : D ⥤ᵇ U :=
      { toFunctor := TwoFibreProductOver.fst U.p 𝒴.val.val.p 𝒳.val.val.p
          p.toFunctor f.hom.hom.toFunctor
        w := TwoFibreProductOver.fst_comp_eq }
    let i := fullSubcategoryBasedInclusion 𝒳 P
    let Z := BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor U.p
        (fullSubcategoryBased 𝒳 P).p
        𝒳.val.val.p p.toFunctor i.toFunctor)
    let z : Z ⥤ᵇ U :=
      { toFunctor := TwoFibreProductOver.fst U.p
          (fullSubcategoryBased 𝒳 P).p
          𝒳.val.val.p p.toFunctor i.toFunctor
        w := TwoFibreProductOver.fst_comp_eq }
    (∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P,
      Nonempty (g.comp i ≅ f.hom.hom)) ↔
      (∃ g : D ⥤ᵇ Z, Nonempty (g.comp z ≅ q)) := by
  intro U p F D q i Z z
  refine Iff.trans (exists_based_factorization_iff f.hom.hom) ?_
  refine Iff.trans ?_
    (TwoFibreProductOver.exists_based_factorization_fst_iff f.hom.hom.w P).symm
  exact ⟨fun hY d => hY _,
    fun hd => forall_prop_of_forall_twoFibreProduct G E hE hPalg f.hom.hom hd⟩

/-- **Stacks 0507**, the factorization criterion. Let `𝒳` be an algebraic stack over `S`
presented by a smooth groupoid in algebraic spaces `G` through an equivalence `E` over the big
fppf site, let `P` cut out an open, closed or locally closed substack of `𝒳`, and let
`f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks. Then `f` factors through the substack, over
the big fppf site and up to a 2-isomorphism, if and only if the base change of `f` along the
presentation `S_U ⟶ 𝒳` factors through the base change of the substack.

The proof is pointwise on both sides, and the content is that membership of the substack is
local on the site; see the module documentation. -/
@[stacks 0507 "factorization_criterion"]
theorem factorsThroughSubstack_iff_presentation
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS)
    (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
    (_hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (E : (quotientStack G).obj ⥤ 𝒳.val.val.obj)
    [E.IsEquivalence]
    (hE : E ⋙ 𝒳.val.val.p = (quotientStack G).p)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : (IsLocallyClosedSubstack 𝒳 P ∨ IsClosedSubstack 𝒳 P) ∨
      ∃ V : OpenSubstack 𝒳, V.property = P)
    (f : 𝒴 ⟶ 𝒳) :
    let U := (fibredCategory B S hS G.objects.obj).val
    let p := (quotientStackProjection G).comp
      (⟨E, hE⟩ : (quotientStack G) ⥤ᵇ 𝒳.val.val)
    let F := TwoFibreProductOver.structureFunctor U.p 𝒴.val.val.p 𝒳.val.val.p
      p.toFunctor f.hom.hom.toFunctor
    let D := BasedCategory.ofFunctor F
    let q : D ⥤ᵇ U :=
      { toFunctor := TwoFibreProductOver.fst U.p 𝒴.val.val.p 𝒳.val.val.p
          p.toFunctor f.hom.hom.toFunctor
        w := TwoFibreProductOver.fst_comp_eq }
    let i := fullSubcategoryBasedInclusion 𝒳 P
    let Z := BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor U.p
        (fullSubcategoryBased 𝒳 P).p
        𝒳.val.val.p p.toFunctor i.toFunctor)
    let z : Z ⥤ᵇ U :=
      { toFunctor := TwoFibreProductOver.fst U.p
          (fullSubcategoryBased 𝒳 P).p
          𝒳.val.val.p p.toFunctor i.toFunctor
        w := TwoFibreProductOver.fst_comp_eq }
    (∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P,
      Nonempty (g.comp i ≅ f.hom.hom)) ↔
      (∃ g : D ⥤ᵇ Z, Nonempty (g.comp z ≅ q)) := by
  obtain ⟨_, hPalg⟩ := isClosedUnderIsomorphisms_and_isAlgebraicStack_of_substack hP
  exact factorsThroughSubstack_iff_presentation_of_isAlgebraicStack 𝒳 𝒴 G _hG E hE P hPalg f

end AlgebraicGeometry.Stack

end
