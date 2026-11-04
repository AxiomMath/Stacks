module
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Pushforward along a continuous, almost cocontinuous functor commutes with connected colimits

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be continuous, so that precomposition with
`u.op` carries sheaves to sheaves and induces `u^s = u^p : Sh(D) ⥤ Sh(C)`. Colimits of sheaves are
*not* computed pointwise: the colimit of a diagram of sheaves is the sheafification of the
presheaf colimit (Stacks 00WI), and `u^s` — which is exact on presheaves, being a precomposition —
in general fails to commute with that sheafification. The obstruction is concentrated on the
objects `V` of `D` that are *sheaf theoretically empty*, i.e. covered by the empty family (Stacks
04B5, 04B6): a presheaf whose sections over every such `V` form a singleton has its
sheafification computed by coverings that `u` can be made to refine, which is Stacks 04B8. If `u`
is moreover *almost cocontinuous* (Stacks 04B7), the sheaf-theoretically empty objects are exactly
where the coverings of `D` that fail to come from `C` are supported, and the obstruction vanishes
for those diagrams whose presheaf colimit is still a singleton over such `V`. A colimit of
singletons over a *connected* index category is a singleton, so this holds for every connected
diagram whose presheaf colimit exists — in particular for pushouts and coequalizers, and for every
finite connected diagram — but not for the empty diagram: `u^s` need not preserve the initial
sheaf.

The motivating case is a closed immersion `i : Z → X` of topological spaces and the continuous
functor `u : X_{Zar} ⥤ Z_{Zar}`, `U ↦ Z ∩ U`, which is almost cocontinuous but not cocontinuous
(Stacks 00XV); the lemma is the site-theoretic form of the classical fact that `i_*` is not exact
on sheaves of sets but is exact on sheaves of abelian groups (Sheaves, Stacks 00AI).

## Main results

*
`Functor.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous`:
  Stacks 04B9 — for `u` continuous and almost cocontinuous, `u^s : Sh(D) ⥤ Sh(C)` preserves
  colimits of every connected shape whose colimits of sets exist.

## Implementation notes

* The source assumes the index category finite and connected; only connectedness is used, so the
  statement is for an arbitrary connected shape `I` such that `Type w` has colimits of shape `I`.
  The step "a finite connected colimit of singleton sets is a singleton" needs connectedness alone
  (`CategoryTheory.Limits.Types.isColimitPUnitCocone`), and otherwise finiteness only supplies the
  existence of the presheaf colimit `colim^{Psh}_i G_i`, which is here the hypothesis
  `HasColimitsOfShape I (Type w)`. Since
  `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits` provides it for every finite `I`
  whose homs lie in the universe of its objects, the source's statement follows by instance
  resolution. Infinite wide pushouts and filtered colimits are covered
  as well: `IsConnected (WidePushoutShape J)` holds for an arbitrary `J`, and every filtered
  category is connected.
* The two cases named in the source, pushouts and coequalizers, follow by applying the statement at
  `WalkingSpan` and `WalkingParallelPair`, which are connected
  (`CategoryTheory.widePushoutShape_connected`, `CategoryTheory.parallel_pair_connected`) and, being
  finite categories in `Type`, satisfy `HasColimitsOfShape _ (Type w)`.
* "Connected" is Mathlib's `CategoryTheory.IsConnected`, which includes nonemptiness. This is
  essential: over the empty index category the statement would assert that `u^s` preserves initial
  objects, which is false for the closed immersion above — `u^s(∅^#)` has a section over any `U`
  with `Z ∩ U = ∅`. For the same reason the hypothesis is not weakened to
  `CategoryTheory.IsPreconnected`.
* The conclusion is a `PreservesColimitsOfShape`, stated for colimit cocones, so no existence of
  colimits in either sheaf category is assumed; where they exist it gives the isomorphism
  `u^s(colim_i G_i) ≅ colim_i u^s(G_i)` via `CategoryTheory.preservesColimitIso`.
* The index category is allowed to live in any universe, with hom types in a universe of their own,
  as `Mathlib.CategoryTheory.Limits.Preserves.Finite` does for `PreservesFiniteColimits`.
* Continuity of `u` is `CategoryTheory.Functor.IsContinuous`, an instance argument, since `u^s` is
  only defined once it is available; almost cocontinuity is `IsAlmostCocontinuous` (Stacks 04B7), a
  `Prop`-valued definition, hence an explicit hypothesis. "Sheaf theoretically empty" is spelled
  `(⊥ : Sieve V) ∈ K V`, which is clause (5) of Stacks 04B6 and equivalent to the definition 04B5.
* `u^s = u^p` is `CategoryTheory.Functor.sheafPushforwardContinuous`, restriction along `u.op`, so
  that `(u^s G).val = u.op ⋙ G.val` holds by definition.
* The two `HasWeakSheafify` assumptions make "the colimit of sheaves is the sheafification of the
  presheaf colimit" available on each side; no left exactness of sheafification is needed. The one
  place the argument uses that the values are sets is that a connected colimit of singletons is a
  singleton; in any category a connected colimit of a constant diagram is the constant value
  (`CategoryTheory.Limits.isColimitConstCocone`).
* The hypothesis `K.WEqualsLocallyBijective (Type w)` is used on `D` only, to know that the unit
  `𝒢 ⟶ 𝒢^#` is locally bijective. On `C` only the implication "`J`-locally bijective implies
  inverted by sheafification" is used, and it needs no hypothesis on `J`: for `f` locally
  bijective, `f ≫ ·` is injective on morphisms into a sheaf because a sheaf is separated along a
  locally surjective morphism, and surjective by gluing over local preimages, whose compatibility
  is local injectivity of `f`. Given `HasWeakSheafify K (Type w)`, local surjectivity of the unit
  holds at every `w`, while local injectivity is the real content of the hypothesis. Mathlib
  provides `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for a site with objects in
  `Type u` and homs in `Type v` and values in `Type (max u v)`, which covers the source's setting of
  small sites and sheaves of sets, and transports it along equivalences of sites
  (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.transport`, `.ofEssentiallySmall`).

## References

* [Stacks 04B9](https://stacks.math.columbia.edu/tag/04B9), whose proof combines Stacks 00WI with
  Stacks 04B8.
-/

section

universe w t t' v₁ v₂ u₁ u₂ v₃ u₃
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.Sites.ConnectedColimitRestriction

section Sheafification

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {A : Type u₃}
  [Category.{v₃} A] [HasWeakSheafify J A]

/-- **A morphism into a sheaf which sheafification inverts exhibits its target as the
sheafification.** Concretely, its sheafification lift is an isomorphism: the lift is a morphism of
sheaves, and it lies in `J.W` because the sheafification unit does and `J.W` has the two out of
three property. -/
private lemma isIso_sheafifyLift {P Q : Cᵒᵖ ⥤ A} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (hη : J.W η) : IsIso (sheafifyLift J η hQ) := by
  refine (ObjectProperty.isLocal_iff_isIso _ _ ((presheafToSheaf J A).obj P).property hQ).1 ?_
  refine MorphismProperty.of_precomp J.W (toSheafify J P) _ (J.W_toSheafify _) ?_
  rewrite [toSheafify_sheafifyLift]
  exact hη

end Sheafification

/-! ### Sheafification inverts locally bijective morphisms -/

section LocallyBijective

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {X Y Z : Cᵒᵖ ⥤ Type w}

/-- A morphism into a sheaf identifies any two sections with the same image under a locally
injective morphism. -/
private lemma app_eq_of_isLocallyInjective (f : X ⟶ Y) [Presheaf.IsLocallyInjective J f]
    (hZ : Presieve.IsSheaf J Z) (a : X ⟶ Z) {U : Cᵒᵖ} {x₁ x₂ : X.obj U}
    (h : f.app U x₁ = f.app U x₂) : a.app U x₁ = a.app U x₂ := by
  refine (hZ.isSeparated _ (Presheaf.equalizerSieve_mem J f x₁ x₂ h)).ext fun V g hg => ?_
  have hg' : X.map g.op x₁ = X.map g.op x₂ := hg
  rw [← NatTrans.naturality_apply a g.op x₁, ← NatTrans.naturality_apply a g.op x₂, hg']

/-- The family `(localPreimage f y).map a` of images under `a` of the local preimages of `y` does
not depend on the choices of local preimages: its value at `p` is `a x` for every section `x` of
`X` that `f` carries to the restriction of `y` along `p`. -/
private lemma map_localPreimage_apply_of_app_eq (f : X ⟶ Y) [Presheaf.IsLocallyInjective J f]
    (hZ : Presieve.IsSheaf J Z) (a : X ⟶ Z) {U : Cᵒᵖ} (y : Y.obj U) {V : C} {p : V ⟶ U.unop}
    (hp : Presheaf.imageSieve f y p) {x : X.obj (op V)} (hx : f.app (op V) x = Y.map p.op y) :
    ((Presieve.FamilyOfElements.localPreimage f y).map a) p hp = a.app (op V) x := by
  refine app_eq_of_isLocallyInjective f hZ a ?_
  simp [Presieve.FamilyOfElements.localPreimage, Presheaf.app_localPreimage, hx]

/-- **The images under `a` of the local preimages of `y` form a compatible family.** Compatibility
over a sieve is compatibility with restriction along each of its arrows, and the restriction along
`q` of a local preimage of `y` along `p` is a local preimage of `y` along `q ≫ p`; two local
preimages of `y` along one arrow have the same image under `f`, hence also under `a`. This is the
one place local injectivity of `f` is used. -/
private lemma compatible_map_localPreimage (f : X ⟶ Y) [Presheaf.IsLocallyInjective J f]
    (hZ : Presieve.IsSheaf J Z) (a : X ⟶ Z) {U : Cᵒᵖ} (y : Y.obj U) :
    ((Presieve.FamilyOfElements.localPreimage f y).map a).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V W p q hp
  rw [Presieve.FamilyOfElements.map_apply, Presieve.FamilyOfElements.map_apply, ←
    NatTrans.naturality_apply a q.op]
  refine app_eq_of_isLocallyInjective f hZ a ?_
  simp [Presieve.FamilyOfElements.localPreimage, NatTrans.naturality_apply f q.op,
    Presheaf.app_localPreimage, ← ConcreteCategory.comp_apply, ← Y.map_comp, ← op_comp]

/-- A morphism into a sheaf extends along a locally bijective morphism: over a section `y` of `Y`
the extension takes the unique amalgamation of `compatible_map_localPreimage`, and both its
naturality and the identity `f ≫ b = a` are instances of the uniqueness of that amalgamation. -/
private lemma exists_comp_eq_of_isLocallyBijective (f : X ⟶ Y) [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f] (hZ : Presieve.IsSheaf J Z) (a : X ⟶ Z) :
    ∃ b : Y ⟶ Z, f ≫ b = a := by
  choose z hz huniq using fun (U : Cᵒᵖ) (y : Y.obj U) =>
    hZ _ (Presheaf.imageSieve_mem J f y) _ (compatible_map_localPreimage f hZ a y)
  refine ⟨{ app := fun U => ↾z U, naturality := fun U₁ U₂ φ => ?_ }, ?_⟩
  · ext y
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    refine (huniq U₂ (Y.map φ y) _ fun V q hq => ?_).symm
    have hx :
      f.app (op V) (Presheaf.localPreimage f (Y.map φ y) q hq) = Y.map (q ≫ φ.unop).op y := by
      rw [Presheaf.app_localPreimage, op_comp, Quiver.Hom.op_unop, Y.map_comp,
        ConcreteCategory.comp_apply]
    have hr : Presheaf.imageSieve f y (q ≫ φ.unop) := ⟨_, hx⟩
    have hz' := hz U₁ y (q ≫ φ.unop) hr
    rw [op_comp, Quiver.Hom.op_unop, Z.map_comp, ConcreteCategory.comp_apply] at hz'
    rw [hz']
    exact map_localPreimage_apply_of_app_eq f hZ a y hr hx
  · ext U x
    simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
      TypeCat.ofHom_apply]
    refine (huniq U (f.app U x) _ fun V p hp => ?_).symm
    rw [map_localPreimage_apply_of_app_eq f hZ a (f.app U x) hp
        (NatTrans.naturality_apply f p.op x),
      ← NatTrans.naturality_apply a p.op x]

/-- A locally surjective morphism is an epimorphism onto sheaves: over a section `y` of `Y` the two
composites exhibit `g₁ y` and `g₂ y` as amalgamations of one and the same family, the local
preimages of `y` pushed forward along `f ≫ g₁ = f ≫ g₂`. -/
private lemma eq_of_comp_eq_of_isLocallySurjective (f : X ⟶ Y) [Presheaf.IsLocallySurjective J f]
    (hZ : Presieve.IsSheaf J Z) {g₁ g₂ : Y ⟶ Z} (h : f ≫ g₁ = f ≫ g₂) : g₁ = g₂ := by
  ext U y
  refine
    hZ.isSeparated _ (Presheaf.imageSieve_mem J f y)
      ((Presieve.FamilyOfElements.localPreimage f y).map (f ≫ g₁)) _ _
      ((Presieve.FamilyOfElements.isAmalgamation_map_localPreimage f y).map g₁) ?_
  rw [h]
  exact (Presieve.FamilyOfElements.isAmalgamation_map_localPreimage f y).map g₂

/-- **Sheafification inverts locally bijective morphisms.** This is the half of
`CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective` which holds without any hypothesis
relating the universe of the values to the universes of the site. -/
private lemma W_of_isLocallyBijective (f : X ⟶ Y) [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f] : J.W f := by
  intro Z hZ
  have hZ' : Presieve.IsSheaf J Z := (isSheaf_iff_isSheaf_of_type J Z).1 hZ
  exact
    ⟨fun _ _ hg => eq_of_comp_eq_of_isLocallySurjective f hZ' hg, fun a =>
      exists_comp_eq_of_isLocallyBijective f hZ' a⟩

end LocallyBijective

/-! ### Connected colimits of singletons -/

section Connected

variable {I : Type t} [Category.{t'} I] [IsConnected I] {D : Type u₂} [Category.{v₂} D]
  [HasColimitsOfShape I (Type w)] {Q : I ⥤ Dᵒᵖ ⥤ Type w} [HasColimit Q]

/-- **A connected colimit of singletons is a singleton.** The sections over `V` of the colimit of a
diagram of presheaves are the colimit of the sections over `V`, so if every presheaf of the diagram
has exactly one section over `V` then the diagram of sections is isomorphic to the constant diagram
at a one point set, whose colimit over a connected index category is that one point set. -/
@[instance_reducible]
private noncomputable def uniqueColimitObj (V : Dᵒᵖ) (h : ∀ i, Unique ((Q.obj i).obj V)) :
    Unique ((colimit Q).obj V) :=
  (colimitObjIsoColimitCompEvaluation Q V ≪≫
    HasColimit.isoOfNatIso (G := Types.constPUnitFunctor.{w} I) (NatIso.ofComponents
      (fun i => Equiv.toIso (letI := h i; Equiv.equivPUnit ((Q.obj i).obj V)))
      fun _ => by ext x; rfl) ≪≫
    Types.colimitConstPUnitIsoPUnit.{w} I).toEquiv.unique

end Connected

/-! ### Transporting local bijectivity along an almost cocontinuous functor -/

section Transfer

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A sieve of `U` is covering as soon as it contains the arrows with sheaf theoretically empty
image and the arrows whose image lies in a covering sieve of `u U`. -/
private lemma mem_of_isAlmostCocontinuous (hu : IsAlmostCocontinuous u J K) {U : C}
    {S : Sieve (u.obj U)} (hS : S ∈ K (u.obj U)) {R : Sieve U}
    (hemp : ∀ ⦃V : C⦄ (g : V ⟶ U), SheafTheoreticallyEmptySite K (u.obj V) → R g)
    (hmem : ∀ ⦃V : C⦄ (g : V ⟶ U), S (u.map g) → R g) : R ∈ J U := by
  obtain ⟨T, hT, hT'⟩ := hu U hS
  exact J.superset_covering (fun V g hg => (hT' g hg).elim (hemp g) (hmem g)) hT

/-- Almost cocontinuity transports local surjectivity from `K` to `J`, provided the morphism is
already surjective over the sheaf theoretically empty objects. -/
private lemma isLocallySurjective_whiskerLeft_op {X Y : Dᵒᵖ ⥤ Type w} (f : X ⟶ Y)
    (hu : IsAlmostCocontinuous u J K) [Presheaf.IsLocallySurjective K f]
    (hf : ∀ V : D, SheafTheoreticallyEmptySite K V → Function.Surjective (f.app (op V))) :
    Presheaf.IsLocallySurjective J (Functor.whiskerLeft u.op f) :=
  ⟨fun {U} s => mem_of_isAlmostCocontinuous u hu
    (Presheaf.imageSieve_mem K f (U := op (u.obj U)) s)
    (fun _ g hV => hf _ hV (Y.map (u.map g).op s)) fun _ _ hg => hg⟩

/-- Almost cocontinuity transports local injectivity from `K` to `J`, provided the morphism is
already injective over the sheaf theoretically empty objects. -/
private lemma isLocallyInjective_whiskerLeft_op {X Y : Dᵒᵖ ⥤ Type w} (f : X ⟶ Y)
    (hu : IsAlmostCocontinuous u J K) [Presheaf.IsLocallyInjective K f]
    (hf : ∀ V : D, SheafTheoreticallyEmptySite K V → Function.Injective (f.app (op V))) :
    Presheaf.IsLocallyInjective J (Functor.whiskerLeft u.op f) := by
  refine ⟨fun {U} x₁ x₂ h => mem_of_isAlmostCocontinuous u hu
    (Presheaf.equalizerSieve_mem K f x₁ x₂ h) (fun V g hV => hf _ hV ?_) fun _ _ hg => hg⟩
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [NatTrans.naturality_apply f (u.map g).op x₁, NatTrans.naturality_apply f (u.map g).op x₂]
  exact congrArg (fun z => Y.map (u.map g).op z) h

/-- **Local form of Stacks 04B8.** If a presheaf `P` on `(D, K)` has exactly one section over every
sheaf theoretically empty object, then `u^p` of the `K`-sheafification unit of `P` is inverted by
`J`-sheafification; equivalently, `u^p(P^#)` is the `J`-sheafification of `u^p P`. Over such an
object `P^#` too has exactly one section, so the unit is bijective there and almost cocontinuity
carries its local bijectivity from `K` to `J`. -/
private lemma W_whiskerLeft_toSheafify [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [K.WEqualsLocallyBijective (Type w)] (hu : IsAlmostCocontinuous u J K) (P : Dᵒᵖ ⥤ Type w)
    (h : ∀ V : D, SheafTheoreticallyEmptySite K V → Unique (P.obj (op V))) :
    J.W (Functor.whiskerLeft u.op (toSheafify K P)) := by
  have hsh : ∀ V : D, SheafTheoreticallyEmptySite K V → Unique ((sheafify K P).obj (op V)) :=
    fun V hV =>
    Types.isTerminalEquivUnique _ (((presheafToSheaf K (Type w)).obj P).isTerminalOfBotCover V hV)
  have :=
    isLocallyInjective_whiskerLeft_op u (toSheafify K P) hu fun V hV x₁ x₂ _ =>
      let := h V hV;
      Subsingleton.elim x₁ x₂
  have :=
    isLocallySurjective_whiskerLeft_op u (toSheafify K P) hu fun V hV _ =>
      let := h V hV;
      let := hsh V hV;
      ⟨default, Subsingleton.elim _ _⟩
  exact W_of_isLocallyBijective _

end Transfer

/-! ### Stacks 04B9 -/

section Main

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {I : Type t} [Category.{t'} I]

/-- The `J`-sheafification lift of `u^p` of the `K`-sheafification unit is compatible with the
colimit cocones on both sides: it is the comparison morphism from the `J`-sheafification of the
`u^p`-image of `E` to the `u^s`-image of the `K`-sheafification of `E`, both of which are colimits
of the restricted diagram. -/
private lemma sheafifyCocone_ι_comp_sheafifyLift [u.IsContinuous J K] [HasWeakSheafify J (Type w)]
    [HasWeakSheafify K (Type w)] (G : I ⥤ Sheaf K (Type w))
    (E : Cocone (G ⋙ sheafToPresheaf K (Type w)))
    (hQ : Presheaf.IsSheaf J (u.op ⋙ sheafify K E.pt)) (i : I) :
    ((Sheaf.sheafifyCocone (F := G ⋙ u.sheafPushforwardContinuous (Type w) J K)
                (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).mapCocone E)).ι.app
            i).hom ≫
        sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt)) hQ =
      Functor.whiskerLeft u.op (((Sheaf.sheafifyCocone E).ι.app i).hom) := by
  have hs :=
    Sheaf.sheafifyCocone_ι_app_val (F := G ⋙ u.sheafPushforwardContinuous (Type w) J K)
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).mapCocone E) i
  rewrite [hs, Sheaf.sheafifyCocone_ι_app_val E i]
  change
    Functor.whiskerLeft u.op (E.ι.app i) ≫
        (toSheafify J (u.op ⋙ E.pt) ≫
          sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt)) hQ) =
      Functor.whiskerLeft u.op (E.ι.app i ≫ toSheafify K E.pt)
  exact
    congrArg (fun m => Functor.whiskerLeft u.op (E.ι.app i) ≫ m)
      (toSheafify_sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt)) hQ)

/-- If `u^p` of the `K`-sheafification unit of the presheaf colimit of a diagram of sheaves is
inverted by `J`-sheafification, then `u^s` preserves that colimit: both the sheafification of the
`J`-presheaf colimit and the restriction of the sheafified `K`-presheaf colimit are colimits of the
restricted diagram, and the comparison between them is the morphism in question. -/
private lemma preservesColimit_of_W [u.IsContinuous J K] [HasColimitsOfShape I (Type w)]
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)] (G : I ⥤ Sheaf K (Type w))
    (E : Cocone (G ⋙ sheafToPresheaf K (Type w))) (hE : IsColimit E)
    (hW : J.W (Functor.whiskerLeft u.op (toSheafify K E.pt))) :
    PreservesColimit G (u.sheafPushforwardContinuous (Type w) J K) := by
  have hQ : Presheaf.IsSheaf J (u.op ⋙ sheafify K E.pt) :=
    ((u.sheafPushforwardContinuous (Type w) J K).obj
        ((presheafToSheaf K (Type w)).obj E.pt)).property
  -- `u^p` is a precomposition, hence preserves the presheaf colimit, whose sheafification is
  -- therefore a colimit of the restricted diagram
  have hcolim :
    IsColimit
      (Sheaf.sheafifyCocone (F := G ⋙ u.sheafPushforwardContinuous (Type w) J K)
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op).mapCocone E)) :=
    Sheaf.isColimitSheafifyCocone _
      (isColimitOfPreserves ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) hE)
  refine preservesColimit_of_preserves_colimit_cocone (Sheaf.isColimitSheafifyCocone E hE) ?_
  set S := (u.sheafPushforwardContinuous (Type w) J K).mapCocone (Sheaf.sheafifyCocone E)
  -- the comparison morphism between the two colimits is the sheafification lift of `u^p` of the
  -- `K`-sheafification unit, and `hW` makes that lift an isomorphism
  have hdesc :
    hcolim.desc S =
      ObjectProperty.homMk (sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt)) hQ) := by
    refine (hcolim.uniq _ _ fun i => ?_).symm
    exact Sheaf.hom_ext (sheafifyCocone_ι_comp_sheafifyLift u G E hQ i)
  have : IsIso ((sheafToPresheaf J (Type w)).map (hcolim.desc S)) := by
    rw [hdesc]
    exact isIso_sheafifyLift _ hQ hW
  have : IsIso (hcolim.desc S) := isIso_of_reflects_iso _ (sheafToPresheaf J (Type w))
  exact IsColimit.ofPointIso hcolim

end Main

end Stacks.Sites.ConnectedColimitRestriction

namespace CategoryTheory.Functor

@[expose] public section

open Stacks.Sites.ConnectedColimitRestriction in
/-- **Stacks 04B9.** Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be continuous and
almost cocontinuous, and assume sheafification of `Type w`-valued presheaves on `(D, K)` inverts
exactly the locally bijective morphisms. Then `u^s = u^p : Sh(D) ⥤ Sh(C)`, restriction of sheaves
of sets along `u.op`, preserves colimits of every connected shape `I` for which `I`-shaped colimits
of sets exist — in particular pushouts (`WalkingSpan`) and coequalizers (`WalkingParallelPair`),
and more generally every finite connected shape. -/
@[stacks 04B9 "For `u` continuous and almost cocontinuous, `u^s = u^p : Sh(D) → Sh(C)` commutes
  with pushouts and coequalizers, and more generally with finite connected colimits."]
public theorem preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
    (hu : IsAlmostCocontinuous u J K) [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [K.WEqualsLocallyBijective (Type w)] (I : Type t) [Category.{t'} I] [IsConnected I]
    [HasColimitsOfShape I (Type w)] :
    PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K) := by
  refine ⟨fun {G} => ?_⟩
  refine
    preservesColimit_of_W u G (colimit.cocone (G ⋙ sheafToPresheaf K (Type w)))
      (colimit.isColimit _) ?_
  -- the presheaf colimit is a connected colimit of sheaves, so it too has exactly one section
  -- over every sheaf theoretically empty object
  have h :
    ∀ V : D,
      SheafTheoreticallyEmptySite K V →
        ∀ i, Unique (((G ⋙ sheafToPresheaf K (Type w)).obj i).obj (op V)) :=
    fun V hV i => Types.isTerminalEquivUnique _ ((G.obj i).isTerminalOfBotCover V hV)
  exact W_whiskerLeft_toSheafify u hu _ fun V hV => uniqueColimitObj (op V) (h V hV)

end

end CategoryTheory.Functor

end

/-!
# The pushforward of a morphism of sites with almost cocontinuous underlying functor

Let `f : D → C` be a morphism of sites (Stacks 00X1): a continuous functor `u : C ⥤ D` in the
*opposite* direction whose induced functor `u_s = f⁻¹` on sheaves of sets is exact. Then `f` is a
morphism of topoi `Sh(D) → Sh(C)` (Stacks 00XC), with inverse image `f⁻¹ = u_s` and pushforward
`f_* = u^s = u^p`, restriction of sheaves along `u.op`.

Colimits of sheaves are not computed pointwise: a colimit of sheaves is the sheafification of the
colimit of the underlying presheaves (Stacks 00WI). The functor `f_*` is precomposition, hence
exact on presheaves, but it does not commute with that sheafification in general. The obstruction
is concentrated on the objects `V` of `D` that are *sheaf theoretically empty*, i.e. carry the
empty covering (Stacks 04B5, 04B6): a presheaf on `D` whose sections over every such `V` form a
singleton has `(u^p G)^# = u^p (G^#)` as soon as `u` is continuous and almost cocontinuous
(Stacks 04B7, 04B8). A colimit of singleton sets over a *connected* index category is a
singleton, so this applies to the presheaf colimit of any connected diagram of sheaves, and `f_*`
commutes with connected colimits — in particular with pushouts and coequalizers.

The motivating case is a closed immersion `i : Z → X` of topological spaces and the continuous
functor `u : X_{Zar} ⥤ Z_{Zar}`, `U ↦ Z ∩ U`, which is almost cocontinuous but not cocontinuous
(Stacks 00XV): `i_*` is not exact on sheaves of sets — it does not preserve the initial sheaf —
but it is exact on sheaves of abelian groups (Sheaves, Stacks 00AI), and Stacks 04BD deduces that
from the present lemma.

## Main results

*
`IsMorphismOfSites.preservesColimitsOfShape_pushforward_morphismOfTopoi_of_isAlmostCocontinuous`:
  Stacks 04BA — for a morphism of sites `f : D → C` given by an almost cocontinuous `u : C ⥤ D`,
  the pushforward `f_* : Sh(D) ⥤ Sh(C)` preserves colimits of every connected shape whose
  colimits exist.

## Implementation notes

* `f_*` is the `pushforward` field of the morphism of topoi `hf.morphismOfTopoi` attached to the
  morphism of sites by Stacks 00XC, which is `u.sheafPushforwardContinuous (Type w) J K` —
  restriction along `u.op`, so that `(f_* G).obj = u.op ⋙ G.obj` holds by definition. The
  statement is thus a special case of Stacks 04B9
  (`preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous` above). As in the
  source, the exactness part of the morphism-of-sites hypothesis is not used.
* As for Stacks 04B9, the statement is for an arbitrary connected shape `I` with
  `[HasColimitsOfShape I (Type w)]` rather than for finite connected shapes; every finite `I`
  satisfies this, and in particular the two cases named in the source, `WalkingSpan` and
  `WalkingParallelPair`, which are connected (`CategoryTheory.widePushoutShape_connected`,
  `CategoryTheory.parallel_pair_connected`).
* `CategoryTheory.IsConnected` includes nonemptiness, and this cannot be dropped: over the empty
  shape the statement would assert that `f_*` preserves initial objects, which is false for the
  closed immersion above — `f_*(∅^#)` has a section over every `U` with `Z ∩ U = ∅`.
* Sheaves are of sets, and the two sites are small with `C`, `D` in one universe, matching the API
  for Stacks 00X1 and 00XC (`CategoryTheory.Functor.IsMorphismOfSites`,
  `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`).

## References

* [Stacks 04BA](https://stacks.math.columbia.edu/tag/04BA), a special case of Stacks 04B9.
-/

section

universe t t' w
open CategoryTheory Limits
variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {u : C ⥤ D}

namespace Stacks.Sites.ConnectedColimitPushforward

/-- The pushforward of the morphism of topoi `Sh(D) → Sh(C)` attached by Stacks 00XC to a morphism
of sites `f : D → C` given by `u : C ⥤ D` is `u^s = u.sheafPushforwardContinuous (Type w) J K`,
restriction of sheaves of sets along `u.op`. This is the defining equation of the `pushforward`
field of `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`, so it holds by `rfl`; it is
stated here because that definition is not tagged `@[simps]` and hence has no projection lemma. -/
private theorem morphismOfTopoi_pushforward (hf : u.IsMorphismOfSites J K) :
    haveI := hf.isContinuous
    hf.morphismOfTopoi.pushforward = u.sheafPushforwardContinuous (Type w) J K :=
  rfl

end Stacks.Sites.ConnectedColimitPushforward

namespace CategoryTheory.Functor.IsMorphismOfSites

@[expose] public section

open Stacks.Sites.ConnectedColimitPushforward in
/-- **Stacks 04BA.** Let `f : D → C` be a morphism of sites (Stacks 00X1) associated to the
continuous functor `u : C ⥤ D`, so that `f_* : Sh(D) ⥤ Sh(C)` is the pushforward of the morphism
of topoi attached to `f` (Stacks 00XC), namely restriction of sheaves of sets along `u.op`. If `u`
is almost cocontinuous (Stacks 04B7), then `f_*` preserves colimits of every connected shape whose
colimits exist — in particular pushouts and coequalizers, which are connected shapes. -/
@[stacks 04BA "For a morphism of sites `f : D → C` whose continuous functor `u : C → D` is almost
  cocontinuous, `f_*` commutes with pushouts and coequalizers, and more generally with finite
  connected colimits."]
public theorem preservesColimitsOfShape_pushforward_morphismOfTopoi_of_isAlmostCocontinuous
    {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {u : C ⥤ D} (hf : u.IsMorphismOfSites J K)
    (hu : IsAlmostCocontinuous u J K) (I : Type t) [Category.{t'} I] [IsConnected I]
    [HasColimitsOfShape I (Type w)] :
    PreservesColimitsOfShape I hf.morphismOfTopoi.pushforward := by
  have := hf.isContinuous
  rw [morphismOfTopoi_pushforward hf]
  exact u.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous J K hu I

end

end CategoryTheory.Functor.IsMorphismOfSites

end
