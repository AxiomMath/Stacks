module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Coproduct inclusions of fppf sheaves are open and closed (Stacks 0F15)

Let `H` be a binary coproduct of `F` and `G` in the category of sheaves of sets on the big
fppf site of `S`. Then the inclusion `F ⟶ H` is representable by open immersions, and also by
closed immersions; by symmetry the same holds for `G ⟶ H`.

The proof is the one indicated by the source, carried out through the *characteristic map* of
the decomposition. Write `I` for the final object `S` of the site and `D` for the object
`S ⨿ S`, which lies in the site because the size cutoff of a big fppf site is closed under
small coproducts. The two inclusions `I ⟶ D` form a Zariski, hence fppf, covering family of
`D` whose members are monomorphisms with initial pairwise intersections, so the representable
sheaf of `D` is the binary coproduct of two copies of the representable sheaf of `I` — that
is, `D` represents the sheaf `2`. Consequently the unique pair of maps `F ⟶ I`, `G ⟶ I`
induces a *characteristic* map `e : H ⟶ h_D`, and because the category of sheaves of sets is
finitary extensive the van Kampen property turns the coproduct cocone into a cartesian
square: `F = H ×_{h_D} h_I`. Representability of `F ⟶ H` is therefore reduced to
representability of `I ⟶ D` in the site, which is the scheme morphism
`coprod.inl : S ⟶ S ⨿ S` — an open *and* a closed immersion, both properties being stable
under base change.

## Main results

* `AlgebraicGeometry.coproductInl_isOpenImmersion`: **Stacks 0F15**, the first coproduct
  inclusion is representable by open immersions.
* `AlgebraicGeometry.coproductInl_isClosedImmersion`: **Stacks 0F15**, the first coproduct
  inclusion is representable by closed immersions.
* `AlgebraicGeometry.coproductInl_pullback_rep` is the common underlying statement: it names
  the object of the site representing the fibre product, together with its cartesian square
  and both immersion properties at once.

## Implementation notes

A coproduct is supplied by its universal binary cocone rather than by a particular chosen
coproduct object, so no choice of `⨿` in the sheaf category is involved and the conclusions
apply to any cocone which happens to be colimiting.

The auxiliary material about the object `S ⨿ S` of the site and about initial objects of the
site is stated separately, since it is the general mechanism by which a two-valued locally
constant function on a scheme of the site is the same thing as a decomposition of that scheme
into two complementary clopen pieces:

* `AlgebraicGeometry.BigFppfSite.contains_coprod_self`, the size bound;
* `AlgebraicGeometry.BigFppfOver.doubleBase` with its two inclusions and
  `AlgebraicGeometry.BigFppfOver.isColimit_yoneda_doubleBaseCofan`, which says that its
  representable sheaf is the coproduct of two copies of the final representable sheaf;
* `AlgebraicGeometry.BigFppfOver.bot_mem_topology_of_isInitial`, that the empty sieve covers
  an initial object, which is what makes the pairwise intersections of that covering family
  vanish. It is proved in `StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties`, together with
  the general statement `AlgebraicGeometry.BigFppfSite.bot_mem_topology` for an object whose
  underlying scheme has no points.

`AlgebraicGeometry.BigFppfSite.generate_mem_topology_of_isFppfCovering` generalizes the
existing `AlgebraicGeometry.BigFppfSite.generate_singleton_mem_topology` from a one-element
family to an arbitrary fppf covering family; both are the combinatorial-representative axiom
of a big fppf site in the form needed to produce a covering sieve.

## References

* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

/-! ### Size bounds and covering families -/

/-- The size cutoff of a big fppf site is closed under the coproduct of a scheme with
itself. -/
theorem BigFppfSite.contains_coprod_self (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) : B.Contains (S ⨿ S) := by
  let Y : ULift.{u} WalkingPair → Scheme.{u} := fun i => i.1.casesOn S S
  have hY : ∀ i, (Y i).size < B.cutoff := by
    rintro ⟨_ | _⟩ <;> simpa [Y] using hS
  have hι : Cardinal.mk (ULift.{u} WalkingPair) ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hsum : (∐ Y).size < B.cutoff :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof hι Y hY
  simpa [Scheme.size_congr (coprodIsoSigma S S)] using hsum

/-- The size cutoff of a big fppf site contains the coproduct of two copies of the base,
written through the inclusion of the site's underlying category into schemes. -/
theorem BigFppfSite.contains_coprod_base (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) :
    B.Contains (B.inclusion.obj (B.obj hS) ⨿ B.inclusion.obj (B.obj hS)) :=
  B.contains_coprod_self hS

/-- The sieve generated by an fppf covering family of a big fppf site is a covering sieve.
This is the combinatorial-representative axiom of a big fppf site: the given family need not
itself satisfy the site's chosen cardinal bound, but it is combinatorially equivalent to one
that does, and combinatorially equivalent families generate the same presieve. -/
alias BigFppfSite.generate_mem_topology_of_isFppfCovering := BigFppfSite.generate_mem_topology

/-- The first inclusion of a scheme into a binary coproduct is a closed immersion: its
complement is the range of the other inclusion, which is open. -/
theorem isClosedImmersion_coprod_inl (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [(isCompl_range_inl_inr X Y).eq_compl]
  exact (IsOpenImmersion.isOpen_range (coprod.inr : Y ⟶ X ⨿ Y)).isClosed_compl

/-- The van Kampen property of a finitary extensive category, in the form used here: given a
binary coproduct `H` of `F` and `G` and maps `f : F ⟶ T`, `g : G ⟶ T` into the first and
second summands of a binary coproduct of `T` with itself, the square expressing `F` as the
part of `H` lying over the first copy of `T` is cartesian. -/
theorem isPullback_inl_of_isColimit_binaryCofan {C : Type*} [Category C] [FinitaryExtensive C]
    {F G H T : C} {iF : F ⟶ H} {iG : G ⟶ H} (hc : IsColimit (BinaryCofan.mk iF iG))
    (cT : BinaryCofan T T) (hcT : IsColimit cT) (f : F ⟶ T) (g : G ⟶ T) :
    IsPullback iF f
      (BinaryCofan.IsColimit.desc hc (f ≫ cT.inl) (g ≫ cT.inr)) cT.inl := by
  let e := BinaryCofan.IsColimit.desc hc (f ≫ cT.inl) (g ≫ cT.inr)
  have hF : f ≫ cT.inl = iF ≫ e := (BinaryCofan.IsColimit.inl_desc hc _ _).symm
  have hG : g ≫ cT.inr = iG ≫ e := (BinaryCofan.IsColimit.inr_desc hc _ _).symm
  exact (((BinaryCofan.isVanKampen_iff cT).mp (FinitaryExtensive.vanKampen cT hcT)
    (BinaryCofan.mk iF iG) f g e hF hG).mp ⟨hc⟩).1

/-! ### The object `S ⨿ S` of the site, and its representable sheaf -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base `S`, regarded as the final object of the big fppf site of `S`. -/
abbrev terminalObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The coproduct `S ⨿ S` of two copies of the base, regarded as an object of the big fppf
site of `S` by the fold map. Its representable sheaf is the sheaf `2`, so a map to it from a
scheme of the site is the same thing as a decomposition of that scheme into two complementary
clopen pieces. -/
noncomputable abbrev doubleBase : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj (B.contains_coprod_base hS)) (Y := B.obj hS)
    (coprod.desc (𝟙 (B.inclusion.obj (B.obj hS))) (𝟙 (B.inclusion.obj (B.obj hS)))))

/-- The first inclusion of the base into `S ⨿ S`, as a morphism of the big fppf site. -/
noncomputable def doubleBaseInl : terminalObj B S hS ⟶ doubleBase B S hS :=
  Over.homMk (B.inclusion.preimage (X := B.obj hS)
    (Y := B.obj (B.contains_coprod_base hS))
    (coprod.inl : B.inclusion.obj (B.obj hS) ⟶
      B.inclusion.obj (B.obj hS) ⨿ B.inclusion.obj (B.obj hS))) (by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage (X := B.obj hS)
        (Y := B.obj (B.contains_coprod_base hS)) coprod.inl ≫
      B.inclusion.preimage (X := B.obj (B.contains_coprod_base hS)) (Y := B.obj hS)
        (coprod.desc (𝟙 (B.inclusion.obj (B.obj hS)))
          (𝟙 (B.inclusion.obj (B.obj hS))))) = B.inclusion.map (𝟙 (B.obj hS))
    rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact coprod.inl_desc _ _)

/-- The second inclusion of the base into `S ⨿ S`, as a morphism of the big fppf site. -/
noncomputable def doubleBaseInr : terminalObj B S hS ⟶ doubleBase B S hS :=
  Over.homMk (B.inclusion.preimage (X := B.obj hS)
    (Y := B.obj (B.contains_coprod_base hS))
    (coprod.inr : B.inclusion.obj (B.obj hS) ⟶
      B.inclusion.obj (B.obj hS) ⨿ B.inclusion.obj (B.obj hS))) (by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage (X := B.obj hS)
        (Y := B.obj (B.contains_coprod_base hS)) coprod.inr ≫
      B.inclusion.preimage (X := B.obj (B.contains_coprod_base hS)) (Y := B.obj hS)
        (coprod.desc (𝟙 (B.inclusion.obj (B.obj hS)))
          (𝟙 (B.inclusion.obj (B.obj hS))))) = B.inclusion.map (𝟙 (B.obj hS))
    rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact coprod.inr_desc _ _)

/-- The underlying scheme morphism of the first inclusion of the base into `S ⨿ S`. -/
theorem doubleBaseInl_left_hom :
    (doubleBaseInl B S hS).left.hom =
      (coprod.inl : B.inclusion.obj (B.obj hS) ⟶
        B.inclusion.obj (B.obj hS) ⨿ B.inclusion.obj (B.obj hS)) :=
  B.inclusion.map_preimage _

/-- The underlying scheme morphism of the second inclusion of the base into `S ⨿ S`. -/
theorem doubleBaseInr_left_hom :
    (doubleBaseInr B S hS).left.hom =
      (coprod.inr : B.inclusion.obj (B.obj hS) ⟶
        B.inclusion.obj (B.obj hS) ⨿ B.inclusion.obj (B.obj hS)) :=
  B.inclusion.map_preimage _

/-- The two inclusions of the base into `S ⨿ S`, as a covering family of the site. -/
noncomputable def doubleBaseCover : PreZeroHypercover (doubleBase B S hS) where
  I₀ := ULift.{u + 1} WalkingPair
  X _ := terminalObj B S hS
  f i := i.down.casesOn (doubleBaseInl B S hS) (doubleBaseInr B S hS)

/-- The two inclusions of the base into `S ⨿ S` form a Zariski, hence fppf, covering
family. -/
theorem isFppfCovering_doubleBaseCover :
    IsFppfCovering ⟨(doubleBase B S hS).left,
      (doubleBaseCover B S hS).map (Over.forget (B.obj hS))⟩ := by
  let T0 := B.inclusion.obj (B.obj hS)
  let E0 := ((doubleBaseCover B S hS).map (Over.forget (B.obj hS))).map B.inclusion
  have hleft : E0.f (ULift.up WalkingPair.left) = (coprod.inl : T0 ⟶ T0 ⨿ T0) :=
    doubleBaseInl_left_hom B S hS
  have hright : E0.f (ULift.up WalkingPair.right) = (coprod.inr : T0 ⟶ T0 ⨿ T0) :=
    doubleBaseInr_left_hom B S hS
  have hZ : E0.presieve₀ ∈ Scheme.zariskiPrecoverage (T0 ⨿ T0) := by
    change Presieve.ofArrows E0.X E0.f ∈ Scheme.zariskiPrecoverage (T0 ⨿ T0)
    apply (Scheme.ofArrows_mem_precoverage_iff
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})).2
    refine ⟨?_, ?_⟩
    · intro x
      rcases (coprodMk T0 T0).surjective x with ⟨y | y, rfl⟩
      · exact ⟨ULift.up WalkingPair.left, y, by rw [hleft, coprodMk_inl]; rfl⟩
      · exact ⟨ULift.up WalkingPair.right, y, by rw [hright, coprodMk_inr]; rfl⟩
    · rintro ⟨_ | _⟩
      · change IsOpenImmersion (E0.f (ULift.up WalkingPair.left))
        rw [hleft]
        exact inferInstanceAs (IsOpenImmersion (coprod.inl : T0 ⟶ T0 ⨿ T0))
      · change IsOpenImmersion (E0.f (ULift.up WalkingPair.right))
        rw [hright]
        exact inferInstanceAs (IsOpenImmersion (coprod.inr : T0 ⟶ T0 ⨿ T0))
  unfold IsFppfCovering
  rw [Precoverage.mem_comap_iff]
  simpa [E0, doubleBaseCover, PreZeroHypercover.presieve₀_map, schemeBelowInclusion,
    toScheme, Over.forget, Functor.map_comp, doubleBase, BigFppfSite.obj, T0] using
    Scheme.zariskiPrecoverage_le_fppfPrecoverage (T0 ⨿ T0) hZ

/-- The two inclusions of the base into `S ⨿ S`, as a cofan of the site. -/
noncomputable def doubleBaseCofan :
    Cofan (fun _ : ULift.{u + 1} WalkingPair => terminalObj B S hS) :=
  Cofan.mk (doubleBase B S hS) fun i =>
    i.down.casesOn (doubleBaseInl B S hS) (doubleBaseInr B S hS)

/-- The sieve generated by the two inclusions of the base into `S ⨿ S` covers. -/
theorem sieve_doubleBaseCofan_mem_topology :
    Sieve.ofArrows _ (doubleBaseCofan B S hS).inj ∈
      BigFppfOver.topology B S hS (doubleBase B S hS) := by
  have hgen := B.generate_mem_topology_of_isFppfCovering
    ((doubleBaseCover B S hS).map (Over.forget (B.obj hS)))
    (isFppfCovering_doubleBaseCover B S hS)
  have heq : Sieve.ofArrows _ (doubleBaseCofan B S hS).inj =
      (Sieve.overEquiv (doubleBase B S hS)).symm
        (Sieve.ofArrows _ (fun i => ((doubleBaseCofan B S hS).inj i).left)) := by
    apply (Sieve.overEquiv (doubleBase B S hS)).injective
    rw [OrderIso.apply_symm_apply]
    exact Sieve.overEquiv_ofArrows (X := B.obj hS) (Y := doubleBase B S hS) _ _
  rw [heq]
  apply B.topology.overEquiv_symm_mem_over
  simpa [doubleBaseCofan, doubleBaseCover, PreZeroHypercover.presieve₀_map,
    Sieve.functorPushforward_overForget_arrows, BigFppfOver.forget] using hgen

end BigFppfOver

/-! ### Initial objects of the site and the empty covering -/

/-- The empty scheme, regarded as an object of the big fppf site of `S`. -/
noncomputable def BigFppfOver.initialObj (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj B.contains_empty) (Y := B.obj hS)
    (Scheme.emptyTo (B.inclusion.obj (B.obj hS))))

/-- The empty scheme is an initial object of the big fppf site of `S`. -/
noncomputable def BigFppfOver.isInitial_initialObj (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsInitial (BigFppfOver.initialObj B S hS) :=
  Over.isInitialOfIsInitialLeft (Y := BigFppfOver.initialObj B S hS)
    (isInitial_schemeBelow B
      (by change IsInitial (∅ : Scheme.{u}); exact AlgebraicGeometry.emptyIsInitial))

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The representable sheaf of `S ⨿ S` is the coproduct of two copies of the representable
sheaf of `S`, i.e. it is the sheaf `2`.

This is the descent criterion for a covering family whose members are monomorphisms with
initial pairwise intersections, applied to the two inclusions of the base into `S ⨿ S`. -/
noncomputable def isColimit_yoneda_doubleBaseCofan
    [(BigFppfOver.topology B S hS).Subcanonical] :
    IsColimit (BinaryCofan.mk
      ((BigFppfOver.topology B S hS).yoneda.map (doubleBaseInl B S hS))
      ((BigFppfOver.topology B S hS).yoneda.map (doubleBaseInr B S hS))) := by
  let J := BigFppfOver.topology B S hS
  let c := doubleBaseCofan B S hS
  let T0 := B.inclusion.obj (B.obj hS)
  let hD : B.Contains (T0 ⨿ T0) := B.contains_coprod_base hS
  have hmono : ∀ i, Mono (c.inj i) := by
    intro i
    apply (Over.forget (B.obj hS)).mono_of_mono_map
    apply B.inclusion.mono_of_mono_map
    rcases i with ⟨_ | _⟩
    · change Mono (B.inclusion.map (B.inclusion.preimage (X := B.obj hS)
        (Y := B.obj hD) (coprod.inl : T0 ⟶ T0 ⨿ T0)))
      rw [B.inclusion.map_preimage]
      infer_instance
    · change Mono (B.inclusion.map (B.inclusion.preimage (X := B.obj hS)
        (Y := B.obj hD) (coprod.inr : T0 ⟶ T0 ⨿ T0)))
      rw [B.inclusion.map_preimage]
      infer_instance
  let : ∀ i, Mono (c.inj i) := hmono
  let hc := J.isColimitCofanMkYoneda
    (X := fun _ : ULift.{u + 1} WalkingPair => terminalObj B S hS) (c := c)
    (sieve_doubleBaseCofan_mem_topology B S hS)
    (bot_mem_topology_of_isInitial B S hS)
    (by
      intro i j hij Y a b hab
      have hIL : (doubleBaseInl B S hS).left.hom = (coprod.inl : T0 ⟶ T0 ⨿ T0) :=
        doubleBaseInl_left_hom B S hS
      have hIR : (doubleBaseInr B S hS).left.hom = (coprod.inr : T0 ⟶ T0 ⨿ T0) :=
        doubleBaseInr_left_hom B S hS
      have hstrict : ∀ (f g : T0 ⟶ T0 ⨿ T0),
          IsPullback (initial.to _) (initial.to _) f g →
          B.inclusion.map a.left ≫ f = B.inclusion.map b.left ≫ g →
          Nonempty (IsInitial Y) := by
        intro f g hpb hab'
        have hP : IsInitial (pullback f g) :=
          IsInitial.ofIso initialIsInitial hpb.isoPullback
        exact ⟨Over.isInitialOfIsInitialLeft (Y := Y) (isInitial_schemeBelow B
          (IsInitial.ofStrict (pullback.lift _ _ hab') hP))⟩
      have hpbLR : IsPullback (initial.to _) (initial.to _)
          (coprod.inl : T0 ⟶ T0 ⨿ T0) coprod.inr :=
        FinitaryExtensive.isPullback_initial_to
          (colimit.isColimit (pair T0 T0)) ⟨WalkingPair.left⟩ ⟨WalkingPair.right⟩ (by decide)
      have h := congrArg (fun f => B.inclusion.map ((Over.forget (B.obj hS)).map f)) hab
      rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
      · exact (hij rfl).elim
      · refine hstrict _ _ hpbLR ?_
        simpa [Functor.map_comp, c, doubleBaseCofan, hIL, hIR] using h
      · refine hstrict _ _ hpbLR.flip ?_
        simpa [Functor.map_comp, c, doubleBaseCofan, hIL, hIR] using h
      · exact (hij rfl).elim)
  refine BinaryCofan.isColimitMk
    (fun s => hc.desc (Cofan.mk s.pt fun i => i.down.casesOn s.inl s.inr)) ?_ ?_ ?_
  · exact fun s => Cofan.IsColimit.fac hc _ (ULift.up WalkingPair.left)
  · exact fun s => Cofan.IsColimit.fac hc _ (ULift.up WalkingPair.right)
  intro s m hmL hmR
  refine Cofan.IsColimit.hom_ext hc m
    (hc.desc (Cofan.mk s.pt fun i => i.down.casesOn s.inl s.inr)) ?_
  rintro ⟨_ | _⟩
  · calc
      J.yoneda.map (c.inj (ULift.up WalkingPair.left)) ≫ m = s.inl := by
        simpa [c, doubleBaseCofan] using hmL
      _ = J.yoneda.map (c.inj (ULift.up WalkingPair.left)) ≫
          hc.desc (Cofan.mk s.pt fun i => i.down.casesOn s.inl s.inr) := by
        symm
        exact Cofan.IsColimit.fac hc _ _
  · calc
      J.yoneda.map (c.inj (ULift.up WalkingPair.right)) ≫ m = s.inr := by
        simpa [c, doubleBaseCofan] using hmR
      _ = J.yoneda.map (c.inj (ULift.up WalkingPair.right)) ≫
          hc.desc (Cofan.mk s.pt fun i => i.down.casesOn s.inl s.inr) := by
        symm
        exact Cofan.IsColimit.fac hc _ _

end BigFppfOver

/-! ### Stacks 0F15 -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F G H : Sheaf (BigFppfOver.topology B S hS) (Type u))
variable (iF : F ⟶ H) (iG : G ⟶ H)

/-- **Stacks 0F15**, in the form carrying the representing object. For a binary coproduct `H`
of sheaves `F` and `G` on the big fppf site of `S` and a section `γ : h_A ⟶ H`, the fibre
product `h_A ×_H F` is represented by an object `P` of the site whose structure morphism
`P ⟶ A` is both an open and a closed immersion of schemes.

Concretely, `γ` composed with the characteristic map of the decomposition is a morphism
`A ⟶ S ⨿ S` of the site, and `P` is the preimage of the first copy of `S`. -/
theorem coproductInl_pullback_rep (hc : IsColimit (BinaryCofan.mk iF iG))
    {A : BigFppfOver B S hS} (γ : yoneda.obj A ⟶ H.obj) :
    ∃ (P : BigFppfOver B S hS) (m : P ⟶ A) (f : yoneda.obj P ⟶ F.obj),
      IsPullback f (yoneda.map m) iF.hom γ ∧
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map m) ∧
        IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) := by
  let J := BigFppfOver.topology B S hS
  let T := BigFppfOver.toScheme B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS)))
  let _ : HasSheafify J (Type u) := hasSheafifyEssentiallySmallSite.{_, _, _, _, u} J _
  let _ : (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let I := BigFppfOver.terminalObj B S hS
  let D := BigFppfOver.doubleBase B S hS
  let inl := BigFppfOver.doubleBaseInl B S hS
  let inr := BigFppfOver.doubleBaseInr B S hS
  let cT : BinaryCofan (J.yoneda.obj I) (J.yoneda.obj I) :=
    BinaryCofan.mk (J.yoneda.map inl) (J.yoneda.map inr)
  let hcT := BigFppfOver.isColimit_yoneda_doubleBaseCofan B S hS
  have hJT : IsTerminal (J.yoneda.obj I) :=
    (Over.mkIdTerminal : IsTerminal I).isTerminalObj J.yoneda
  let γS : J.yoneda.obj A ⟶ H := (fullyFaithfulSheafToPresheaf J (Type u)).preimage γ
  let f₀ : F ⟶ J.yoneda.obj I := hJT.from F
  let g₀ : G ⟶ J.yoneda.obj I := hJT.from G
  let e : H ⟶ J.yoneda.obj D := BinaryCofan.IsColimit.desc hc (f₀ ≫ cT.inl) (g₀ ≫ cT.inr)
  have hpb₁ : IsPullback iF f₀ e cT.inl := by
    with_unfolding_all exact isPullback_inl_of_isColimit_binaryCofan hc cT hcT f₀ g₀
  let d : A ⟶ D := J.yonedaEquiv (γS ≫ e)
  have hd : J.yoneda.map d = γS ≫ e :=
    J.yonedaEquiv.injective (J.yonedaEquiv_yoneda_map d)
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let P := pullback inl d
  let m : P ⟶ A := pullback.snd inl d
  let p : P ⟶ I := pullback.fst inl d
  have hpb₂site : IsPullback p m inl d := IsPullback.of_hasPullback inl d
  have hpb₂ : IsPullback (J.yoneda.map p) (J.yoneda.map m)
      (J.yoneda.map inl) (J.yoneda.map d) := hpb₂site.map J.yoneda
  let f : J.yoneda.obj P ⟶ F := hpb₁.isLimit.lift
    (PullbackCone.mk (J.yoneda.map m ≫ γS) (J.yoneda.map p) (by
      rw [Category.assoc, ← hd]
      exact hpb₂.w.symm))
  have hf₀ : f ≫ f₀ = J.yoneda.map p := PullbackCone.IsLimit.lift_snd _ _ _ _
  have hfH : f ≫ iF = J.yoneda.map m ≫ γS := PullbackCone.IsLimit.lift_fst _ _ _ _
  have hpb : IsPullback f (J.yoneda.map m) iF γS :=
    IsPullback.of_right (by rwa [hf₀, ← hd]) hfH hpb₁.flip
  have hpb₂T : IsPullback (T.map p) (T.map m) (T.map inl) (T.map d) := by
    let _ : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape WalkingCospan :=
      schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan _
    let _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
    let _ : PreservesLimit (cospan inl d) T := inferInstance
    exact hpb₂site.map T
  have hOpenInl : IsOpenImmersion (T.map inl) := by
    change IsOpenImmersion inl.left.hom
    rw [BigFppfOver.doubleBaseInl_left_hom]
    infer_instance
  have hClosedInl : IsClosedImmersion (T.map inl) := by
    change IsClosedImmersion inl.left.hom
    rw [BigFppfOver.doubleBaseInl_left_hom]
    exact isClosedImmersion_coprod_inl _ _
  refine ⟨P, m, f.hom, ?_, MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb₂T
    hOpenInl, MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb₂T hClosedInl⟩
  have hγ : γS.hom = γ := rfl
  simpa [GrothendieckTopology.yonedaCompSheafToPresheaf, hγ] using
    hpb.map (sheafToPresheaf J (Type u))

/-- **Stacks 0F15.** The first inclusion into a binary coproduct of sheaves on the big fppf
site of `S` is representable by open immersions. By symmetry the same holds for the second
inclusion. -/
@[stacks 0F15 "open immersion"]
theorem coproductInl_isOpenImmersion (hc : IsColimit (BinaryCofan.mk iF iG)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) iF.hom := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun A γ => ?_
  obtain ⟨P, m, f, hpb, hopen, -⟩ :=
    coproductInl_pullback_rep B S hS F G H iF iG hc γ
  exact ⟨P, f, m, hpb, hopen⟩

/-- **Stacks 0F15.** The first inclusion into a binary coproduct of sheaves on the big fppf
site of `S` is representable by closed immersions. By symmetry the same holds for the second
inclusion. -/
@[stacks 0F15 "closed immersion"]
theorem coproductInl_isClosedImmersion (hc : IsColimit (BinaryCofan.mk iF iG)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) iF.hom := by
  let _ : MorphismProperty.RespectsIso
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.mk <;>
      intro X Y Z e g hg <;> infer_instance
  let _ : (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  refine MorphismProperty.relative.of_exists fun A γ => ?_
  obtain ⟨P, m, f, hpb, -, hclosed⟩ :=
    coproductInl_pullback_rep B S hS F G H iF iG hc γ
  exact ⟨P, f, m, hpb, hclosed⟩

end AlgebraicGeometry

end
