module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelInjective

/-!
# Stacks 0D0X: local generation of `ε^*𝒦₀` by the sections `m_h`

Part of the proof of Stacks 0D0X: every section of the degree `-1` cohomology
sheaf `𝒦₀` of `NL_{X₀/Y₀}` over an open `O` of an affine Zariski square `Z ⊆ f_0^{-1}W` is, on an
open covering of `O`, a combination of the restrictions of the sections `m_h` attached to the
chart classes `h ∈ H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})`.  Locally the section comes from `H₁` of the
sections (`Stacks.SheafOfModules.sectionsH1LiftSieve_mem`), and a class of `H₁` of the sections
comes locally from `𝒪_{X₀} ⊗ H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)})`
(`Stacks.NaiveCotangentZariskiChart.liftSieve_mem`, Stacks 0D08 at the points); the classes of
`H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)})` are those of the étale chart through `𝒪_X(ε Z) = Γ(X₀, Z)`.

## Main results

* `Stacks.SheafOfModules.exists_covering_kernel_ι_eq_sectionsH1NaiveCotangent`: a section of the
  degree `-1` cohomology sheaf of `NL_{B/A}` is, on a covering, the image of a class of `H₁` of
  the sections.
* `AlgebraicGeometry.Space.sectionsH1Restrict_representedChartToZariskiH1`: the Zariski chart map
  factors through the étale chart.
* `AlgebraicGeometry.Space.exists_covering_mem_representedZariskiKernelSpan`: local generation of
  `𝒦₀` by the `m_h`.
* `AlgebraicGeometry.Space.exists_covering_representedKernelTensorModel`: every section of the
  pullback model `𝒪_X ⊗ 𝒦₀` over a chart over `ε Z` lies locally in the image of `ρ`
  (pulled back along `ε`, which is cover preserving, so that its left adjoint `L` is
  cocontinuous).
* `AlgebraicGeometry.Space.exists_covering_representedEpsilonKernelPullbackModel_map_eq_zero`:
  a section of `𝒪_X ⊗ 𝒦₀` over such a chart killed by the model of the adjunct of `κ_{-1}`
  vanishes locally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.NaiveCotangent

/-- **Pasting two squares into a given one, on first homology**, with every ring structure a
free variable (so that the lemma applies by unification whatever the spelling of the instances). -/
theorem h1CotangentMapOfSquare_comp_of_eq {R S R' S' R'' S'' : Type*} {_ : CommRing R}
    {_ : CommRing S} {_ : CommRing R'} {_ : CommRing S'} {_ : CommRing R''} {_ : CommRing S''}
    {_ : Algebra R S} {_ : Algebra R' S'} {_ : Algebra R'' S''}
    {fR : R →+* R'} {fS : S →+* S'} {h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r)}
    {gR : R' →+* R''} {gS : S' →+* S''}
    {h' : ∀ r : R', gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r)}
    {kR : R →+* R''} {kS : S →+* S''}
    {hk : ∀ r : R, kS (algebraMap R S r) = algebraMap R'' S'' (kR r)}
    (eR : gR.comp fR = kR) (eS : gS.comp fS = kS) (x : Algebra.H1Cotangent R S) :
    h1CotangentMapOfSquare gR gS h' (h1CotangentMapOfSquare fR fS h x) =
      h1CotangentMapOfSquare kR kS hk x :=
  (h1CotangentMapOfSquare_comp fR fS h gR gS h' x).trans
    (h1CotangentMapOfSquare_congr _ hk eR eS x)

/-- **Pasting three squares into a given one, on first homology**, with every ring structure a
free variable. -/
theorem h1CotangentMapOfSquare_comp_comp_of_eq {R S R' S' R'' S'' R''' S''' : Type*}
    {_ : CommRing R} {_ : CommRing S} {_ : CommRing R'} {_ : CommRing S'} {_ : CommRing R''}
    {_ : CommRing S''} {_ : CommRing R'''} {_ : CommRing S'''}
    {_ : Algebra R S} {_ : Algebra R' S'} {_ : Algebra R'' S''} {_ : Algebra R''' S'''}
    {fR : R →+* R'} {fS : S →+* S'} {h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r)}
    {gR : R' →+* R''} {gS : S' →+* S''}
    {h' : ∀ r : R', gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r)}
    {lR : R'' →+* R'''} {lS : S'' →+* S'''}
    {h'' : ∀ r : R'', lS (algebraMap R'' S'' r) = algebraMap R''' S''' (lR r)}
    {kR : R →+* R'''} {kS : S →+* S'''}
    {hk : ∀ r : R, kS (algebraMap R S r) = algebraMap R''' S''' (kR r)}
    (eR : lR.comp (gR.comp fR) = kR) (eS : lS.comp (gS.comp fS) = kS)
    (x : Algebra.H1Cotangent R S) :
    h1CotangentMapOfSquare lR lS h''
        (h1CotangentMapOfSquare gR gS h' (h1CotangentMapOfSquare fR fS h x)) =
      h1CotangentMapOfSquare kR kS hk x :=
  (congrArg (h1CotangentMapOfSquare lR lS h'')
      (h1CotangentMapOfSquare_comp fR fS h gR gS h' x)).trans
    (h1CotangentMapOfSquare_comp_of_eq eR eS x)

end Stacks.NaiveCotangent

namespace Stacks.PullbackModel

/-- **Induction on the extension of scalars `B ⊗_A M`**: a property of its elements holding at
the pure tensors and stable under sums holds everywhere. -/
theorem extendScalars_induction {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat.{u} A} {p : (ModuleCat.extendScalars f).obj M → Prop}
    (tmul : ∀ (b : B) (m : M), p (Stacks.PullbackModel.tmul f b m))
    (add : ∀ x y, p x → p y → p (x + y)) (x : (ModuleCat.extendScalars f).obj M) : p x :=
  TensorProduct.inductionOn x tmul add

/-- **Images of a span**: if `Ψ b` is additive in its second argument, moves scalars into the
first one, and every generator `m` has `Ψ b m` in the image of `ρ` for all `b`, so has every
element of the span. -/
theorem forall_exists_eq_of_mem_span {R M P T β : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [AddCommGroup T] (ρ : T →+ P) (Ψ : β → M → P)
    (hΨ0 : ∀ b, Ψ b 0 = 0) (hΨadd : ∀ b x y, Ψ b (x + y) = Ψ b x + Ψ b y) (σ : R → β → β)
    (hΨsmul : ∀ b a x, Ψ b (a • x) = Ψ (σ a b) x) {s : Set M}
    (hs : ∀ m ∈ s, ∀ b, ∃ t, ρ t = Ψ b m) {x : M} (hx : x ∈ Submodule.span R s) :
    ∀ b, ∃ t, ρ t = Ψ b x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact fun b => ⟨0, ρ.map_zero.trans (hΨ0 b).symm⟩
  | add x y _ _ hx hy =>
    intro b
    obtain ⟨t₁, e₁⟩ := hx b
    obtain ⟨t₂, e₂⟩ := hy b
    exact ⟨t₁ + t₂, (ρ.map_add t₁ t₂).trans ((congrArg₂ (· + ·) e₁ e₂).trans (hΨadd b x y).symm)⟩
  | smul a x _ hx =>
    intro b
    obtain ⟨t, e⟩ := hx (σ a b)
    exact ⟨t, e.trans (hΨsmul b a x).symm⟩

/-- **Sections locally in the image of a family `ρ` of additive maps form an additive
subgroup**: sums of such sections are such sections. -/
theorem exists_covering_map_add {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (P : _root_.PresheafOfModules R) (J : GrothendieckTopology C) {Y : C} {T : Over Y → Type*}
    [∀ V, AddCommGroup (T V)] (ρ : ∀ V : Over Y, T V →+ ToType (P.obj (op V.left))) {V' : Over Y}
    (x y : ToType (P.obj (op V'.left)))
    (hx : ∃ R : Sieve V', R ∈ J.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = P.map g.left.op x)
    (hy : ∃ R : Sieve V', R ∈ J.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = P.map g.left.op y) :
    ∃ R : Sieve V', R ∈ J.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = P.map g.left.op (x + y) := by
  obtain ⟨R₁, h₁, e₁⟩ := hx
  obtain ⟨R₂, h₂, e₂⟩ := hy
  refine ⟨R₁ ⊓ R₂, GrothendieckTopology.intersection_covering _ h₁ h₂, fun V'' g hg => ?_⟩
  obtain ⟨t₁, f₁⟩ := e₁ g hg.1
  obtain ⟨t₂, f₂⟩ := e₂ g hg.2
  exact ⟨t₁ + t₂, (map_add _ t₁ t₂).trans ((congrArg₂ (· + ·) f₁ f₂).trans
    (map_add (P.map g.left.op).hom x y).symm)⟩

end Stacks.PullbackModel

namespace Stacks.PullbackLeftAdjoint

universe w

/-- **Local generation of a pullback model from its pure tensors**: if every pure tensor of
`O(V) ⊗ M(L V)` restricts, on a covering of `V`, into the images of a family `ρ` of additive
maps, so does every section. -/
theorem exists_covering_pullbackModel_of_tmul {C : Type*} [Category C] {D : Type*} [Category D]
    {F : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ F) {O₀ : Cᵒᵖ ⥤ CommRingCat.{w}}
    {O : Dᵒᵖ ⥤ CommRingCat.{w}} (φ : O₀ ⟶ F.op ⋙ O)
    (M : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat))
    (K : GrothendieckTopology D) {Y : D} {T : Over Y → Type*} [∀ V, AddCommGroup (T V)]
    (ρ : ∀ V : Over Y, T V →+ ToType (((pullbackModel adj φ).obj M).obj (op V.left)))
    (V' : Over Y)
    (htmul : ∀ b m, ∃ R : Sieve V', R ∈ K.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = ((pullbackModel adj φ).obj M).map g.left.op
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app (op V'.left)).hom b m))
    (w : ToType (((pullbackModel adj φ).obj M).obj (op V'.left))) :
    ∃ R : Sieve V', R ∈ K.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = ((pullbackModel adj φ).obj M).map g.left.op w := by
  refine Stacks.PullbackModel.extendScalars_induction
    ((transposeRingHom adj φ).app (op V'.left)).hom
    (p := fun w => ∃ R : Sieve V', R ∈ K.over Y V' ∧ ∀ ⦃V'' : Over Y⦄ (g : V'' ⟶ V'), R g →
      ∃ t, ρ V'' t = ((pullbackModel adj φ).obj M).map g.left.op w) htmul ?_ w
  intro x y hx hy
  exact Stacks.PullbackModel.exists_covering_map_add _ K ρ x y hx hy

end Stacks.PullbackLeftAdjoint

namespace Stacks.UniverseLift

universe v₇ u₇ r₇ m₇ z₇

variable {C : Type u₇} [Category.{v₇} C] {J : GrothendieckTopology C}

/-- A section of `N`, read as a section of its transport to the lifted ring. -/
def ringTransportSection (O : Sheaf J CommRingCat.{r₇})
    (N : _root_.SheafOfModules.{m₇} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ)
    (m : ToType (N.val.obj X)) :
    ToType (((ringTransportEquivalence.{m₇, z₇} O).functor.obj N).val.obj X) :=
  m

/-- A sum, read in the transport to the lifted ring, is the sum of the summands read there. -/
theorem ringTransportSection_add (O : Sheaf J CommRingCat.{r₇})
    (N : _root_.SheafOfModules.{m₇} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ)
    (m m' : ToType (N.val.obj X)) :
    ringTransportSection.{v₇, u₇, r₇, m₇, z₇} O N X (m + m') =
      ringTransportSection O N X m + ringTransportSection O N X m' :=
  rfl

/-- The zero section, read in the transport to the lifted ring, is zero. -/
theorem ringTransportSection_zero (O : Sheaf J CommRingCat.{r₇})
    (N : _root_.SheafOfModules.{m₇} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ) :
    ringTransportSection.{v₇, u₇, r₇, m₇, z₇} O N X 0 = 0 :=
  rfl

/-- **A multiple, read in the transport to the lifted ring**, is the multiple by the lifted
scalar. -/
theorem ringTransportSection_smul (O : Sheaf J CommRingCat.{r₇})
    (N : _root_.SheafOfModules.{m₇} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ)
    (r : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X))
    (m : ToType (N.val.obj X)) :
    ringTransportSection.{v₇, u₇, r₇, m₇, z₇} O N X (r • m) =
      (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z₇} O)).obj.obj X)
        from ULift.up.{z₇} r) • ringTransportSection O N X m :=
  rfl

end Stacks.UniverseLift

namespace Stacks.SheafOfModules

universe v₁ u₁ w₁ z₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {_ : HasWeakSheafify J CommRingCat.{w₁}}
  [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})] in
/-- **Restriction of `H₁` of the sections along a morphism of a slice, under the image in
`NL^{-1}`**: it is the restriction of `H₁` of the sections of the restricted presheaves of
rings. -/
theorem sectionsH1NaiveCotangent_restrict_over_left
    [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})] {Z : C}
    [LocallySmall.{w₁} (Over Z)] (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) {X Y : Over Z}
    (g : Y ⟶ X)
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj (op X.left))) (ToType (B.obj.obj (op X.left))) _ _
      (algebraSections J A B a (op X.left)))
    (w : Stacks.NaiveCotangent.H1Tensor.H1X ((Over.forget Z).op ⋙ A.obj)
      ((Over.forget Z).op ⋙ B.obj) (Functor.whiskerLeft (Over.forget Z).op a.hom) Y)
    (hw : Stacks.NaiveCotangent.H1Tensor.h1Restrict ((Over.forget Z).op ⋙ A.obj)
        ((Over.forget Z).op ⋙ B.obj) (Functor.whiskerLeft (Over.forget Z).op a.hom) g z = w) :
    sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a (op Y.left)
        (sectionsH1Restrict J A B a g.left.op z) =
      sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a (op Y.left) w :=
  congrArg _ hw

/-- **The image of `H₁` of the sections in `NL^{-1}` commutes with restriction.** -/
theorem sectionsH1NaiveCotangent_restrict (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B)
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj X)) (ToType (B.obj.obj X)) _ _
      (algebraSections J A B a X)) :
    sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a Y (sectionsH1Restrict J A B a f z) =
      ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).X (-1)).val.map f
        (sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a X z) :=
  (congrArg _ (sectionsH1Comparison_restrict.{v₁, u₁, w₁, z₁} J A B a f z)).trans
    (PresheafOfModules.naturality_apply
      (eqToHom (naiveCotangentComplex_X_negOne.{v₁, u₁, w₁, z₁} J A B a).symm).val f _)

/-- If a section of `𝒦₀` has image the image of a class of `H₁` of the sections, so does its
restriction. -/
private theorem kernel_ι_map_eq_sectionsH1_restrict
    (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : ToType ((kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.obj X))
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj X)) (ToType (B.obj.obj X)) _ _
      (algebraSections J A B a X))
    (h : (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.app X m =
      sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a X z) :
    (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.app Y
        ((kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.map f m) =
      sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a Y (sectionsH1Restrict J A B a f z) :=
  ((PresheafOfModules.naturality_apply
    (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val f m).trans
      (congrArg _ h)).trans (sectionsH1NaiveCotangent_restrict J A B a f z).symm

/-- **A section of the degree `-1` cohomology sheaf of `NL_{B/A}` comes locally from `H₁` of the
sections**: on a covering of `X`, its image in `NL^{-1}` is the image of a class of
`H₁(L_{B(Y)/A(Y)})`. -/
theorem exists_covering_kernel_ι_eq_sectionsH1NaiveCotangent
    (_ : J.WEqualsLocallyBijective CommRingCat.{w₁}) (A B : Sheaf J CommRingCat.{w₁})
    (a : A ⟶ B) {X : C}
    (k : ToType ((kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.obj
      (op X))) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ ⦃Y : C⦄ (g : Y ⟶ X), S g →
      ∃ z : @Algebra.H1Cotangent (ToType (A.obj.obj (op Y))) (ToType (B.obj.obj (op Y))) _ _
          (algebraSections J A B a (op Y)),
        (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.app (op Y)
            ((kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.map g.op k) =
          sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a (op Y) z := by
  let e := canonicalConormalKernelIso.{v₁, u₁, w₁, z₁} J A B a
  let k' := e.inv.val.app (op X) k
  let c := (kernel.ι (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f).val.app (op X) k'
  have hc : (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f.val.app (op X) c = 0 :=
    (congrArg (fun t => t.val.app (op X) k') (kernel.condition
      (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f)).trans rfl
  refine ⟨sectionsH1LiftSieve.{v₁, u₁, w₁, z₁} J A B a c,
    sectionsH1LiftSieve_mem.{v₁, u₁, w₁, z₁} J A B a c hc, ?_⟩
  rintro Y g ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have h1 := canonicalConormalKernelIso_hom_app_ι.{v₁, u₁, w₁, z₁} J A B a (op Y)
    ((kernel (presentationConormalSequence.{v₁, u₁, w₁, z₁} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f).val.map g.op k') z
    ((PresheafOfModules.naturality_apply (kernel.ι (presentationConormalSequence.{v₁, u₁, w₁, z₁}
      J A B a (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).f).val g.op k').trans
        hz.symm)
  refine Eq.trans ?_ h1
  refine congrArg _ ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply e.hom.val g.op k').symm
  exact congrArg _ (ConcreteCategory.congr_hom (congrArg (fun t => t.val.app (op X))
    e.inv_hom_id) k).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V) {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}

/-- **The inverse square of the identifications `𝒪_X(ε Z) = Γ(X₀, Z)`, `𝒪_Y(ε W) = Γ(Y₀, W)`
commutes**: `Γ(Y₀, W) ⟶ Γ(X₀, Z) ⟶ 𝒪_X(ε Z)` is `Γ(Y₀, W) ⟶ 𝒪_Y(ε W) ⟶ 𝒪_X(ε Z)`. -/
theorem representedZariskiToChart_comm (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (r : Γ((BigFppfOver.toScheme B S hS).obj V, W)) :
    (Scheme.Opens.topIso Z).inv.hom
        (@algebraMap _ _ _ _ (Stacks.NaiveCotangentZariskiChart.chartAlgebra
          ((BigFppfOver.toScheme B S hS).map φ) hZW) r) =
      @algebraMap _ _ _ _ (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW)) ((Scheme.Opens.topIso W).inv.hom r) := by
  have e1 := representedChartToZariski_comm B S hS φ hZW ((Scheme.Opens.topIso W).inv.hom r)
  have e2 : representedChartToZariskiBase B S hS φ hZW ((Scheme.Opens.topIso W).inv.hom r) =
      (Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom r :=
    congrArg (Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom
      (ConcreteCategory.congr_hom (Scheme.Opens.topIso W).inv_hom_id r)
  rw [e2] at e1
  have e3 := ConcreteCategory.congr_hom (Scheme.Hom.inverseImageSections_comp
    ((BigFppfOver.toScheme B S hS).map φ) hZW) r
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).hom_inv_id _)
  exact congrArg (Scheme.Opens.topIso Z).inv.hom (e3.symm.trans e1.symm)

/-- **The Zariski chart class carried to the étale chart**: the map
`H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)}) ⟶ H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})` of the identifications of the rings. -/
abbrev representedZariskiChartH1ToChart (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
    (Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW)
    (chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (Scheme.Opens.topIso W).inv.hom (Scheme.Opens.topIso Z).inv.hom
    (representedZariskiToChart_comm B S hS φ hZW)

/-- **The Zariski chart map at `U ⊆ Z` factors through the étale chart**: the image of a class
`h₀ ∈ H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)})` in `H₁` of the sections over `U` is the restriction to `U` of
the image of the corresponding étale chart class in `H₁` of the sections over `Z`. -/
theorem sectionsH1Restrict_representedChartToZariskiH1
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (U' : Over Z)
    (h₀ : @Algebra.H1Cotangent Γ((BigFppfOver.toScheme B S hS).obj V, W)
        Γ((BigFppfOver.toScheme B S hS).obj U, Z) _ _
        (Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ)
          hZW)) :
    letI := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
    Stacks.SheafOfModules.sectionsH1Restrict
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
        (representedZariskiSchemeHom B S hS φ).fSharpInverseImage U'.hom.op
        (representedChartToZariskiH1 B S hS φ hZW
          (representedZariskiChartH1ToChart B S hS φ hZW h₀)) =
      Stacks.NaiveCotangent.H1Tensor.h1Map
        (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
        (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
        (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
        Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
        (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
        Stacks.NaiveCotangentZariskiChart.structureMap
        (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ) hZW)
        U' h₀ := by
  let := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := representedZariskiAlgebra B S hS φ Z
  let := representedZariskiAlgebra B S hS φ U'.left
  refine Stacks.NaiveCotangent.h1CotangentMapOfSquare_comp_comp_of_eq ?_ ?_ h₀
  · refine RingHom.ext fun r => ?_
    exact congrArg (fun x => ((((inverseImageCommRingFunctor
      (representedZariskiSchemeHom B S hS φ).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.map U'.hom.op).hom
          ((Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom x)))
      (ConcreteCategory.congr_hom (Scheme.Opens.topIso W).inv_hom_id r)
  · refine RingHom.ext fun r => ?_
    exact congrArg (fun x => (((BigFppfOver.toScheme B S hS).obj U).sheaf.obj.map
      U'.hom.op).hom x) (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).inv_hom_id r)

/-- `m_h|_O`, for an open `O ⊆ Z`. -/
abbrev representedZariskiKernelSectionOver (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (O : Over Z) (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op O.left)) :=
  (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map O.hom.op
    (representedZariskiKernelSection B S hS φ hZW h)

/-- **The span of the sections `m_h|_O`** in the sections over `O ⊆ Z` of the degree `-1`
cohomology sheaf `𝒦₀` of `NL_{X₀/Y₀}`. -/
abbrev representedZariskiKernelSpan (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (O : Over Z) :
    Submodule (ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj (op O.left)))
      (ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
        (op O.left))) :=
  Submodule.span _ (Set.range (representedZariskiKernelSectionOver B S hS φ hZW O))

/-- `𝒪_{X₀}(O) ⊗_{Γ(X₀, Z)} H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)})`, the source of `τ₀` at `O ⊆ Z`. -/
abbrev representedZariskiChartTensor (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (O : Over Z) : Type u :=
  letI := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
  letI := Stacks.NaiveCotangent.H1Tensor.algΓ
    (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
    Γ((BigFppfOver.toScheme B S hS).obj U, Z) Stacks.NaiveCotangentZariskiChart.structureMap O
  TensorProduct Γ((BigFppfOver.toScheme B S hS).obj U, Z)
    (ToType ((Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z)).obj (op O)))
    (Algebra.H1Cotangent Γ((BigFppfOver.toScheme B S hS).obj V, W)
      Γ((BigFppfOver.toScheme B S hS).obj U, Z))

/-- **The image of `s • m_{h}|_O` in `NL^{-1}`**, for the étale chart class `h` of a Zariski
chart class `h₀`, is the image of `s • τ₀(h₀)`. -/
theorem kernel_ι_smul_representedZariskiKernelSectionOver
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (O : Over Z)
    (s : ToType ((Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z)).obj (op O)))
    (h₀ : @Algebra.H1Cotangent Γ((BigFppfOver.toScheme B S hS).obj V, W)
        Γ((BigFppfOver.toScheme B S hS).obj U, Z) _ _
        (Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ)
          hZW)) :
    letI := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
    letI := representedZariskiAlgebra B S hS φ O.left
    (kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
        (op O.left)
        ((show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj (op O.left)) from s) •
          representedZariskiKernelSectionOver B S hS φ hZW O
            (representedZariskiChartH1ToChart B S hS φ hZW h₀)) =
      Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
        (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op O.left)
        ((show ToType (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O.obj.obj
          (op O.left)) from s) •
          (show @Algebra.H1Cotangent _ _ _ _ (representedZariskiAlgebra B S hS φ O.left) from
            Stacks.NaiveCotangent.H1Tensor.h1Map
            (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
            (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
            (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
            Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
            (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
            Stacks.NaiveCotangentZariskiChart.structureMap
            (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ)
              hZW) O h₀)) := by
  let := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
  let := representedZariskiAlgebra B S hS φ O.left
  refine (((kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
    (op O.left)).hom.map_smul _ _).trans ?_
  refine Eq.trans ?_ (Stacks.SheafOfModules.sectionsH1NaiveCotangent_smul.{u, u, u, u + 1} _ _ _
    _ _ s _).symm
  refine congrArg (_ • ·) ?_
  refine (Stacks.SheafOfModules.kernel_ι_map_eq_sectionsH1_restrict.{u, u, u, u + 1}
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J _ _ _ O.hom.op _ _
    (kernel_ι_representedZariskiKernelSection B S hS φ hZW _)).trans ?_
  exact congrArg _ (sectionsH1Restrict_representedChartToZariskiH1 B S hS φ hZW O h₀)

/-- **`τ₀` lands in the span of the `m_h|`**: the image in `NL^{-1}` of `τ₀(t)`, for
`t ∈ 𝒪_{X₀}(O) ⊗_{Γ(X₀, Z)} H₁(L_{Γ(X₀, Z)/Γ(Y₀, W)})`, is the image of an element of the span
of the sections `m_h|_O`. -/
theorem exists_mem_representedZariskiKernelSpan
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (O : Over Z)
    (t : representedZariskiChartTensor B S hS φ hZW O) :
    letI := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
    ∃ x ∈ representedZariskiKernelSpan B S hS φ hZW O,
      (kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
          (op O.left) x =
        Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
          ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
          (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op O.left)
          (Stacks.NaiveCotangent.H1Tensor.h1Tensor
            (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
            (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
            (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
            Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
            (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
            Stacks.NaiveCotangentZariskiChart.structureMap
            (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ)
              hZW) O t) := by
  let := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
  let := Stacks.NaiveCotangent.H1Tensor.algΓ
    (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
    Γ((BigFppfOver.toScheme B S hS).obj U, Z) Stacks.NaiveCotangentZariskiChart.structureMap O
  let ι := ((kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
    (op O.left)).hom
  let τ := Stacks.NaiveCotangent.H1Tensor.h1Tensor
    (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
    (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
    (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
    Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
    (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
    Stacks.NaiveCotangentZariskiChart.structureMap
    (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ) hZW) O
  induction t using TensorProduct.inductionOn with
  | tmul s h₀ =>
    have e1 := kernel_ι_smul_representedZariskiKernelSectionOver B S hS φ hZW O s h₀
    have e2 := Stacks.NaiveCotangent.H1Tensor.h1Tensor_tmul
            (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
            (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
            (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
            Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
            (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
            Stacks.NaiveCotangentZariskiChart.structureMap
            (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ)
              hZW) O s h₀
    have e3 := congrArg (Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
          ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
          (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op O.left)) e2.symm
    exact ⟨(show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj (op O.left)) from s) •
      representedZariskiKernelSectionOver B S hS φ hZW O
        (representedZariskiChartH1ToChart B S hS φ hZW h₀),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩), e1.trans e3⟩
  | add x y hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, (ι.map_add a b).trans ?_⟩
    refine (congrArg₂ (· + ·) ea eb).trans ?_
    refine (Stacks.SheafOfModules.sectionsH1NaiveCotangent_add.{u, u, u, u + 1} _ _ _ _ _ _
      _).symm.trans ?_
    exact congrArg _ (τ.map_add x y).symm

/-- **Local generation of `𝒦₀` by the sections `m_h`**: over an affine Zariski square
`Z ⊆ f_0^{-1}W`, every section of the degree `-1` cohomology sheaf `𝒦₀` of `NL_{X₀/Y₀}` over an
open `O ⊆ Z` lies, on an open covering of `O`, in the span of the restrictions of the `m_h`. -/
theorem exists_covering_mem_representedZariskiKernelSpan
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) (O : Over Z)
    (k : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op O.left))) :
    ∃ R : Sieve O, R ∈ (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj U)).over Z O ∧
      ∀ ⦃O' : Over Z⦄ (g : O' ⟶ O), R g →
        (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map
            g.left.op k ∈ representedZariskiKernelSpan B S hS φ hZW O' := by
  let := Stacks.NaiveCotangentZariskiChart.chartAlgebra ((BigFppfOver.toScheme B S hS).map φ) hZW
  obtain ⟨S₁, hS₁, h₁⟩ :=
    Stacks.SheafOfModules.exists_covering_kernel_ι_eq_sectionsH1NaiveCotangent.{u, u, u, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J inferInstance _ _
      (representedZariskiSchemeHom B S hS φ).fSharpInverseImage k
  have h₁' : ∀ ⦃O'' : Over Z⦄ (g : O'' ⟶ O), (Sieve.overEquiv O).symm S₁ g → _ :=
    fun O'' g hg => h₁ g.left ((Sieve.overEquiv_symm_iff _ _).1 hg)
  choose z hz using h₁'
  refine ⟨Sieve.bind ((Sieve.overEquiv O).symm S₁) fun O'' g hg =>
    Stacks.NaiveCotangent.H1Tensor.liftSieve
      (Stacks.NaiveCotangentZariskiChart.baseRestrict ((BigFppfOver.toScheme B S hS).map φ))
      (Stacks.NaiveCotangentZariskiChart.structureRestrict (Z := Z))
      (Stacks.NaiveCotangentZariskiChart.sharpRestrict ((BigFppfOver.toScheme B S hS).map φ))
      Γ((BigFppfOver.toScheme B S hS).obj V, W) Γ((BigFppfOver.toScheme B S hS).obj U, Z)
      (Stacks.NaiveCotangentZariskiChart.baseMap ((BigFppfOver.toScheme B S hS).map φ) hZW)
      (Stacks.NaiveCotangentZariskiChart.baseMap_restrict ((BigFppfOver.toScheme B S hS).map φ) hZW)
      Stacks.NaiveCotangentZariskiChart.structureMap
      Stacks.NaiveCotangentZariskiChart.structureMap_restrict
      (Stacks.NaiveCotangentZariskiChart.chartSquare ((BigFppfOver.toScheme B S hS).map φ) hZW)
      O'' (z g hg), ?_, ?_⟩
  · refine GrothendieckTopology.bind_covering _
      ((Opens.grothendieckTopology _).overEquiv_symm_mem_over O S₁ hS₁) ?_
    intro O'' g hg
    exact Stacks.NaiveCotangentZariskiChart.liftSieve_mem ((BigFppfOver.toScheme B S hS).map φ)
      hZW hW hZ O'' (z g hg)
  · rintro O' _ ⟨O'', g', g, hg, ⟨t, ht⟩, rfl⟩
    obtain ⟨x, hx, ex⟩ := exists_mem_representedZariskiKernelSpan B S hS φ hZW O' t
    suffices e : (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map
        (g' ≫ g).left.op k = x by
      rwa [e]
    apply Stacks.SheafOfModules.injective_app_kernel_ι _ (op O'.left)
    refine Eq.trans ?_ ex.symm
    refine (congrArg _ ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1)
      0)).val.map_comp_apply g.left.op g'.left.op k)).trans ?_
    refine (Stacks.SheafOfModules.kernel_ι_map_eq_sectionsH1_restrict.{u, u, u, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J _ _ _ g'.left.op _ _
      (hz g hg)).trans ?_
    exact Stacks.SheafOfModules.sectionsH1NaiveCotangent_restrict_over_left.{u, u, u, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J _ _ _ g' (z g hg) _ ht.symm

/-- The pullback model `V ↦ 𝒪_X(V) ⊗_{𝒪_{X₀}(L V)} 𝒦₀(L V)` of `ε^*𝒦₀`, over the lifted rings. -/
abbrev representedEpsilonKernelPullbackModel :=
  (Stacks.PullbackLeftAdjoint.pullbackModel (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).obj
    ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val

/-- `(b, x) ↦ b ⊗ x`, from `𝒪_X(V)` and the sections of `𝒦₀` over `L V` to the pullback model
at `V`. -/
abbrev representedEpsilonKernelTmul (V' : SmallEtale B S hS (yoneda.obj U))
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V')))
    (x : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V')))) :
    ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V')) :=
  Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V') b
    (Stacks.UniverseLift.ringTransportSection.{u, u, u, u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)) _ x)

/-- `b ⊗ 0 = 0` in the pullback model of `ε^*𝒦₀`. -/
theorem representedEpsilonKernelTmul_zero (V' : SmallEtale B S hS (yoneda.obj U))
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V'))) :
    representedEpsilonKernelTmul B S hS φ V' b 0 = 0 :=
  (congrArg _ (Stacks.UniverseLift.ringTransportSection_zero.{u, u, u, u + 1, u + 1} _ _ _)).trans
    (Stacks.PullbackModel.tmul_zero_right _ b)

/-- `b ⊗ (x + y) = b ⊗ x + b ⊗ y` in the pullback model of `ε^*𝒦₀`. -/
theorem representedEpsilonKernelTmul_add (V' : SmallEtale B S hS (yoneda.obj U))
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V')))
    (x y : ToType
      ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
        (op ((representedImageOpenFunctor B S hS U).obj V')))) :
    representedEpsilonKernelTmul B S hS φ V' b (x + y) =
      representedEpsilonKernelTmul B S hS φ V' b x + representedEpsilonKernelTmul B S hS φ V' b y :=
  (congrArg _
      (Stacks.UniverseLift.ringTransportSection_add.{u, u, u, u + 1, u + 1} _ _ _ x y)).trans
    (Stacks.PullbackModel.tmul_add_right _ b _ _)

/-- `b ⊗ (a • x) = (a' * b) ⊗ x` in the pullback model of `ε^*𝒦₀`, where `a'` is the image of
the lifted scalar `a` under the transpose ring map at `V'`. -/
theorem representedEpsilonKernelTmul_smul (V' : SmallEtale B S hS (yoneda.obj U))
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V')))
    (a : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj
        (op ((representedImageOpenFunctor B S hS U).obj V'))))
    (x : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V')))) :
    representedEpsilonKernelTmul B S hS φ V' b (a • x) =
      representedEpsilonKernelTmul B S hS φ V'
        (representedLiftedTranspose B S hS V' (ULift.up.{u + 1} a) * b) x :=
  (congrArg _
      (Stacks.UniverseLift.ringTransportSection_smul.{u, u, u, u + 1, u + 1} _ _ _ a x)).trans
    (Stacks.PullbackModel.tmul_smul_right _ b _ _)

/-- **A pure tensor `b ⊗ x` with `x` in the span of the `m_h|` lies in the image of `ρ`.** -/
theorem tmul_mem_range_representedKernelTensorModel
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V' : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (x : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V'.left))))
    (i : (representedImageOpenFunctor B S hS U).obj V'.left ⟶ Z)
    (hx : x ∈ representedZariskiKernelSpan B S hS φ hZW (Over.mk i)) :
    ∀ b, ∃ t, representedKernelTensorModel B S hS φ hZW V' t =
      representedEpsilonKernelTmul B S hS φ V'.left b x := by
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := chartDiagramRestrictAlgebra B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) V'
  refine Stacks.PullbackModel.forall_exists_eq_of_mem_span
    (representedKernelTensorModel B S hS φ hZW V') (representedEpsilonKernelTmul B S hS φ V'.left)
    (representedEpsilonKernelTmul_zero B S hS φ V'.left)
    (representedEpsilonKernelTmul_add B S hS φ V'.left)
    (fun (a : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj
        (op ((representedImageOpenFunctor B S hS U).obj V'.left)))) b =>
      representedLiftedTranspose B S hS V'.left (ULift.up.{u + 1} a) * b)
    (representedEpsilonKernelTmul_smul B S hS φ V'.left) ?_ hx
  rintro _ ⟨h, rfl⟩ b
  refine ⟨b.down ⊗ₜ h, ?_⟩
  exact congrArg (fun (j : (representedImageOpenFunctor B S hS U).obj V'.left ⟶ Z) =>
    representedEpsilonKernelTmul B S hS φ V'.left b
      ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map j.op
        (representedZariskiKernelSection B S hS φ hZW h))) (Subsingleton.elim _ _)

/-- **The image open functor is cocontinuous**: `ε` is cover preserving, being continuous. -/
theorem isCocontinuous_representedImageOpenFunctor (T : BigFppfOver B S hS) :
    (representedImageOpenFunctor B S hS T).IsCocontinuous
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS T)).J
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedTopos.J :=
  (Adjunction.isCocontinuous_iff_coverPreserving _ _
    (representedImageOpenEpsilonAdjunction B S hS T)).2 (CoverPreserving.of_isContinuous _ _ _)

/-- **Restriction of a pure tensor in the pullback model**, along a morphism of charts over the
chart of a Zariski square. -/
theorem representedEpsilonKernelPullbackModel_map_tmul_over
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V₁ V₂ : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V₂ ⟶ V₁)
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V₁.left)))
    (x : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V₁.left)))) :
    (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op
        (representedEpsilonKernelTmul B S hS φ V₁.left b x) =
      representedEpsilonKernelTmul B S hS φ V₂.left
        (((Stacks.UniverseLift.sheafRingULift.{u + 1}
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.map
            g.left.op).hom b)
        ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map
          ((representedImageOpenFunctor B S hS U).map g.left).op x) :=
  rfl

/-- **The restriction of `b ⊗ x` lies in the image of `ρ`** as soon as the restriction of `x` lies
in the span of the `m_h|`. -/
theorem exists_representedKernelTensorModel_eq_map_tmul
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V₁ V₂ : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V₂ ⟶ V₁)
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V₁.left)))
    (x : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V₁.left))))
    (i : (representedImageOpenFunctor B S hS U).obj V₂.left ⟶ Z)
    (hx : (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map
        ((representedImageOpenFunctor B S hS U).map g.left).op x ∈
      representedZariskiKernelSpan B S hS φ hZW (Over.mk i)) :
    ∃ t, representedKernelTensorModel B S hS φ hZW V₂ t =
      (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op
        (representedEpsilonKernelTmul B S hS φ V₁.left b x) := by
  obtain ⟨t, ht⟩ := tmul_mem_range_representedKernelTensorModel B S hS φ hZW V₂ _ i hx
    (((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.map
        g.left.op).hom b)
  exact ⟨t, ht.trans (representedEpsilonKernelPullbackModel_map_tmul_over B S hS φ hZW g b x).symm⟩

/-- **Local generation of the pullback model on a pure tensor**: over an affine Zariski square,
`b ⊗ k` restricts, on a covering of the chart `V` over `ε Z`, into the image of `ρ`. -/
theorem exists_covering_representedEpsilonKernelTmul
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) (V' : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (b : ToType ((Stacks.UniverseLift.sheafRingULift.{u + 1}
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj.obj (op V'.left)))
    (k : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op ((representedImageOpenFunctor B S hS U).obj V'.left)))) :
    ∃ R : Sieve V', R ∈ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J.over
        (representedEpsilonChartDiagram B S hS φ hZW).U V' ∧
      ∀ ⦃V'' : Over (representedEpsilonChartDiagram B S hS φ hZW).U⦄ (g : V'' ⟶ V'), R g →
        ∃ t, representedKernelTensorModel B S hS φ hZW V'' t =
          (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op
            (representedEpsilonKernelTmul B S hS φ V'.left b k) := by
  have := isCocontinuous_representedImageOpenFunctor B S hS U
  let O : Over Z := Over.mk (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V'.left
    Z).symm V'.hom)
  obtain ⟨R₀, hR₀, hgen⟩ := exists_covering_mem_representedZariskiKernelSpan B S hS φ hZW hZ hW O k
  refine ⟨(Sieve.overEquiv V').symm ((Sieve.overEquiv O R₀).functorPullback
    (representedImageOpenFunctor B S hS U)), ?_, ?_⟩
  · exact GrothendieckTopology.overEquiv_symm_mem_over _ V' _
      (Functor.cover_lift (representedImageOpenFunctor B S hS U)
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        ((GrothendieckTopology.mem_over_iff _ _).1 hR₀))
  · intro V'' g hg
    have h1 : (Sieve.overEquiv O R₀) ((representedImageOpenFunctor B S hS U).map g.left) :=
      (Sieve.overEquiv_symm_iff _ _).1 hg
    have h2 := (Sieve.overEquiv_iff _ _).1 h1
    have hx := hgen _ h2
    exact exists_representedKernelTensorModel_eq_map_tmul B S hS φ hZW g b k _ hx

/-- **Local generation of the pullback model by `ρ`**: over an affine Zariski square, every
section of `𝒪_X ⊗ 𝒦₀` over a chart `V` over `ε Z` restricts, on a covering of `V`, into the image
of `ρ`. -/
theorem exists_covering_representedKernelTensorModel
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) (V' : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (w : ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V'.left))) :
    ∃ R : Sieve V', R ∈ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J.over
        (representedEpsilonChartDiagram B S hS φ hZW).U V' ∧
      ∀ ⦃V'' : Over (representedEpsilonChartDiagram B S hS φ hZW).U⦄ (g : V'' ⟶ V'), R g →
        ∃ t, representedKernelTensorModel B S hS φ hZW V'' t =
          (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op w := by
  have G := Stacks.PullbackLeftAdjoint.exists_covering_pullbackModel_of_tmul
    (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))
    ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (fun V'' => representedKernelTensorModel B S hS φ hZW V'') V'
  have H : ∀ b m, _ := fun b m =>
    exists_covering_representedEpsilonKernelTmul B S hS φ hZW hZ hW V' b m
  exact G H w

/-- The model of the adjunct of `κ_{-1}` kills the restrictions of a section it kills. -/
theorem representedEpsilonKernelModel_app_map_eq_zero {V₁ V₂ : SmallEtale B S hS (yoneda.obj U)}
    (f : V₂ ⟶ V₁) (w : ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V₁)))
    (hw : (representedEpsilonKernelModel B S hS φ).app (op V₁) w = 0) :
    (representedEpsilonKernelModel B S hS φ).app (op V₂)
      ((representedEpsilonKernelPullbackModel B S hS φ).map f.op w) = 0 :=
  (PresheafOfModules.naturality_apply (representedEpsilonKernelModel B S hS φ) f.op w).trans
    ((congrArg _ hw).trans (map_zero _))

/-- A section of the image of `ρ` killed by the model vanishes on the vanishing sieve. -/
theorem chartTensorVanishingSieve_mem_of_eq_map
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) {V' V'' : Over (representedEpsilonChartDiagram B S hS φ hZW).U}
    (g : V'' ⟶ V') (w : ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V'.left)))
    (hw : (representedEpsilonKernelModel B S hS φ).app (op V'.left) w = 0)
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V'')
    (ht : representedKernelTensorModel B S hS φ hZW V'' t =
      (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op w) :
    chartTensorVanishingSieve B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V'' t ∈
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J.over
        (representedEpsilonChartDiagram B S hS φ hZW).U V'' :=
  chartTensorVanishingSieve_mem_of_representedEpsilonKernelModel B S hS φ hZW hZ hW V'' t
    ((congrArg _ ht).trans (representedEpsilonKernelModel_app_map_eq_zero B S hS φ g.left w hw))

/-- On the vanishing sieve of a preimage under `ρ` of `w|`, the section `w` restricts to `0`. -/
theorem representedEpsilonKernelPullbackModel_map_comp_eq_zero
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V' V'' V₃ : Over (representedEpsilonChartDiagram B S hS φ hZW).U}
    (g : V'' ⟶ V') (g' : V₃ ⟶ V'')
    (w : ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V'.left)))
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V'')
    (ht : representedKernelTensorModel B S hS φ hZW V'' t =
      (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op w)
    (hg' : chartTensorVanishingSieve B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V'' t g') :
    (representedEpsilonKernelPullbackModel B S hS φ).map (g' ≫ g).left.op w = 0 := by
  refine ((representedEpsilonKernelPullbackModel B S hS φ).map_comp_apply g.left.op g'.left.op
    w).trans ?_
  refine (congrArg _ ht.symm).trans ?_
  refine (representedKernelTensorModel_restrict_eq_zero B S hS φ hZW g' t hg').trans ?_
  exact (representedKernelTensorModel B S hS φ hZW V₃).map_zero

/-- **Local injectivity of the model on an affine Zariski square**: a section of `𝒪_X ⊗ 𝒦₀` over a
chart over `ε Z` killed by the model of the adjunct of `κ_{-1}` restricts to `0` on a covering. -/
theorem exists_covering_representedEpsilonKernelPullbackModel_map_eq_zero
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) (V' : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (w : ToType ((representedEpsilonKernelPullbackModel B S hS φ).obj (op V'.left)))
    (hw : (representedEpsilonKernelModel B S hS φ).app (op V'.left) w = 0) :
    ∃ R : Sieve V', R ∈ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J.over
        (representedEpsilonChartDiagram B S hS φ hZW).U V' ∧
      ∀ ⦃V'' : Over (representedEpsilonChartDiagram B S hS φ hZW).U⦄ (g : V'' ⟶ V'), R g →
        (representedEpsilonKernelPullbackModel B S hS φ).map g.left.op w = 0 := by
  obtain ⟨R, hR, hgen⟩ := exists_covering_representedKernelTensorModel B S hS φ hZW hZ hW V' w
  choose t ht using hgen
  refine ⟨Sieve.bind R fun V'' g hg => chartTensorVanishingSieve B S hS
    (representedSpaceMap B S hS φ) (representedEpsilonChartDiagram B S hS φ hZW) V'' (t g hg),
    GrothendieckTopology.bind_covering _ hR fun V'' g hg =>
      chartTensorVanishingSieve_mem_of_eq_map B S hS φ hZW hZ hW g w hw (t g hg) (ht g hg), ?_⟩
  rintro V₃ _ ⟨V'', g', g, hg, hg', rfl⟩
  exact representedEpsilonKernelPullbackModel_map_comp_eq_zero B S hS φ hZW g g' w (t g hg)
    (ht g hg) hg'

end AlgebraicGeometry.Space

end
