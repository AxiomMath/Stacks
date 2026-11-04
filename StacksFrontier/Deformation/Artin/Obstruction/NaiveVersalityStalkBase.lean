module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityRestriction

/-!
# Changing the deformation base from the local ring of `S` to an affine open

`Deformation.Artin.IsVersalAt` unfolds (`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`)
to a lifting property quantified over the surjections of
`Deformation.ArtinianLocalAlgCat (𝒪_{S,s}) κ`: the deformation base is the **local ring of `S`
at the image of the point**. The algebra of [Stacks, Tag 07YM]'s direction `(1) ⇒ (2)` in degree
`-1`, by contrast, happens over the ring `Λ` of the affine open the family maps into — the small
extension it builds is `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` with everything in sight a `Λ`-algebra, and
`A` itself is not an `𝒪_{S,s}`-algebra at all. The two vocabularies have to be joined before the
chain can be assembled.

This file joins them in the direction the argument needs: it turns the lifting property over
`𝒪_{S,s}` into the same property over `Λ`. The content is that an Artinian local `Λ`-algebra
whose residue point is the chosen one is *canonically* an `𝒪_{S,s}`-algebra:
`Deformation.Artin.exists_localHom_fromSpecStalk` factors `Spec C ⟶ Spec Λ ⟶ S` through
`Spec 𝒪_{S,s}` by a local homomorphism, and `Deformation.Artin.localHom_fromSpecStalk_injective`
makes that factorization unique, hence compatible with every morphism of `𝒞_Λ` and with the
identification of the residue field. So `𝒞_Λ` maps to `𝒞_{𝒪_{S,s}}` without changing carriers,
morphisms or residue identifications, and the lifting property pulls back along it.

## Main definitions

* `Deformation.Artin.stalkAlgebra` — the `𝒪_{S,s}`-algebra structure on an object of `𝒞_Λ`
  whose residue point is the chosen one, with `Deformation.Artin.isLocalHom_stalkAlgebra` and
  `Deformation.Artin.specMap_stalkAlgebra_comp_fromSpecStalk` its two defining properties.
* `Deformation.Artin.stalkObj` — the resulting object of `𝒞_{𝒪_{S,s}}`, and
  `Deformation.Artin.stalkHom` the resulting morphism.

## Main results

* `Deformation.Artin.residueMap_stalkAlgebra` — the composite `𝒪_{S,s} ⟶ C ⟶ κ` is the
  structure map of `κ` over `𝒪_{S,s}`. This is what makes the residue identification of
  `Deformation.Artin.stalkObj` an `𝒪_{S,s}`-algebra isomorphism, and it is the uniqueness
  clause applied at the field `κ`.
* `Deformation.Artin.hom_comp_stalkAlgebra` — a morphism of `𝒞_Λ` is automatically
  `𝒪_{S,s}`-linear.
* `Deformation.Artin.liftsAtResiduePoint_changeBase` — **the transfer**: the lifting property
  over `𝒪_{S,s}` implies the lifting property over `Λ`.
* `Deformation.Artin.liftsAtResiduePoint_base_of_isVersalAt` — the transfer composed with
  `Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`: versality at `u₀` gives the lifting
  property with *any* `Spec Λ ⟶ S` as deformation base. This is the form the degree `-1` half of
  the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] consumes.

Because the transfer goes this way, no comparison of `Ω_{B/Λ}` with `Ω_{B/𝒪_{S,s}}` is needed
anywhere: the whole of the degree `-1` argument — the small extension, its essential
surjectivity through `Deformation.Artin.differentialsBaseChangeMap`, and the section that
contradicts it — stays over `Λ`, and the only thing that crosses to the local ring is the
lifting property itself.

## Implementation notes

The hypothesis each object carries is `hres`, that the residue point of `C` read through its
structure morphism to `S` is the chosen residue point of `S`. That is the *only* input, and it
is not an extra assumption on the tag: inside
`Deformation.Artin.liftsAtResiduePoint_changeBase` it is **derived** for both algebras of a
lifting problem — for the target from the residue condition the lifting property already
imposes on the arrow `a`, through `Deformation.Artin.schemeMap_over`, and for the source from
the `Λ`-linearity of the surjection together with its compatibility with the residue
identifications. Nothing is asked of `iΛ`: it is *not* assumed to be an open immersion, nor a
monomorphism, and `𝒪_{S,s}` is never identified with a localization of `Λ`. The factorization
is produced at the level of schemes, where only locality of the ring maps is used, so the
ring-level statement "a map into an Artinian local ring factors through `Λ_𝔮`" — which would
need `iΛ` to be an open immersion — is not needed and is not proved here.

The algebra structure of `κ` over `𝒪_{S,s}` is a **named instance binder** together with the
locality of its structure map: that instance is not synthesizable, and `letI` does not fix it.
Locality is what makes the closed point of `Spec κ` land on `s`, which is what
`Deformation.Artin.exists_localHom_fromSpecStalk` asks for.

`Deformation.Artin.stalkObj` reuses the carrier, the ring, the Artinian and local structures
and the underlying equivalence of residue fields of its input, replacing only the algebra
structure and the `commutes'` field. Everything else being literally reused is what makes
`Deformation.Artin.residueMap_stalkObj` and the two surjectivity transfers hold by `rfl`, and
it is what makes `Deformation.Artin.schemeMap` at the two presentations of one base the same
morphism: the two identifications are proofs of equalities between the same pair of objects,
so proof irrelevance identifies the `eqToHom`s they contribute.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

/-! ### The canonical `𝒪_{S,s}`-algebra structure on an object of `𝒞_Λ` -/

section StalkAlgebra

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) (s : S)
  [algStalk : Algebra (S.presheaf.stalk s) k]
  (hloc : IsLocalHom (algebraMap (S.presheaf.stalk s) k))
  (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
  (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s)

/-- The map to the fixed residue field is a local homomorphism: it is the residue map followed
by an isomorphism. -/
public theorem isLocalHom_residueMap : IsLocalHom (residueMap C) := by
  refine ⟨fun a ha => notMem_maximalIdeal.mp fun hmem => ha.ne_zero ?_⟩
  have hzero : residue (C : Type u) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  show C.residueEquiv (residue (C : Type u) a) = 0
  rw [hzero, map_zero]

include hloc hres in
/-- The closed point of `Spec C` maps to the chosen point of `S`: the residue point of `C`
factors through its closed point, both structure maps being local. This is the hypothesis of
`Deformation.Artin.exists_localHom_fromSpecStalk`. -/
public theorem closedPoint_comp_algebraMap_eq :
    (Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ)
      (closedPoint (C : Type u)) = s := by
  have := isLocalHom_residueMap C
  have : IsLocalHom (CommRingCat.ofHom (residueMap C)).hom := isLocalHom_residueMap C
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)).hom := hloc
  have h := congrArg (fun g : Spec (CommRingCat.of k) ⟶ S => g (closedPoint k)) hres
  rw [closedPoint_comp_eq (CommRingCat.ofHom (residueMap C))
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ),
    closedPoint_comp_eq (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k))
      (S.fromSpecStalk s), Scheme.fromSpecStalk_closedPoint] at h
  exact h

/-- **The canonical `𝒪_{S,s}`-algebra structure on an object of `𝒞_Λ`.** An Artinian local
`Λ`-algebra whose residue point is the chosen point of `S` is an algebra over the local ring of
`S` there: `Deformation.Artin.exists_localHom_fromSpecStalk` factors the structure morphism
`Spec C ⟶ Spec Λ ⟶ S` through `Spec 𝒪_{S,s}`.

The factorization is unique among local homomorphisms
(`Deformation.Artin.localHom_fromSpecStalk_injective`), so nothing depends on the choice; that
uniqueness is what `Deformation.Artin.residueMap_stalkAlgebra` and
`Deformation.Artin.hom_comp_stalkAlgebra` are. -/
@[instance_reducible]
public def stalkAlgebra : Algebra (S.presheaf.stalk s) (C : Type u) :=
  (Classical.choose (exists_localHom_fromSpecStalk S s
    (Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ)
    (closedPoint_comp_algebraMap_eq iΛ s hloc C hres))).toAlgebra

/-- The structure map of `Deformation.Artin.stalkAlgebra` is a local homomorphism. -/
public theorem isLocalHom_stalkAlgebra :
    letI := stalkAlgebra iΛ s hloc C hres
    IsLocalHom (algebraMap (S.presheaf.stalk s) (C : Type u)) :=
  (Classical.choose_spec (exists_localHom_fromSpecStalk S s
    (Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ)
    (closedPoint_comp_algebraMap_eq iΛ s hloc C hres))).1

/-- The structure morphism `Spec C ⟶ S` factors through `Spec 𝒪_{S,s}` by
`Deformation.Artin.stalkAlgebra`. This is the identification of the two presentations of the
base of a deformation problem, over `Λ` and over the local ring. -/
public theorem specMap_stalkAlgebra_comp_fromSpecStalk :
    letI := stalkAlgebra iΛ s hloc C hres
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (C : Type u))) ≫
        S.fromSpecStalk s =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ :=
  (Classical.choose_spec (exists_localHom_fromSpecStalk S s
    (Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ)
    (closedPoint_comp_algebraMap_eq iΛ s hloc C hres))).2

/-- Two local homomorphisms out of the stalk of `X` at `x` into `T` agree if they induce the same
morphism `Spec T ⟶ X`; here one of them is a composite `φ ∘ a` through a local map `a`. -/
private theorem comp_eq_of_specMap_comp_fromSpecStalk (X : Scheme.{u}) (x : X)
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing T]
    (φ : R →+* T) (a : X.presheaf.stalk x →+* R) (g : X.presheaf.stalk x →+* T)
    [IsLocalHom φ] [IsLocalHom a] [IsLocalHom g] {P : Spec (CommRingCat.of R) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk x = P)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom φ) ≫ P) : φ.comp a = g := by
  have : IsLocalHom (φ.comp a) := RingHom.isLocalHom_comp _ _
  refine localHom_fromSpecStalk_injective X x _ _ ?_
  rw [hg, ← h, ← Category.assoc, ← Spec.map_comp]
  rfl

include hloc hres in
/-- **The residue identification is `𝒪_{S,s}`-linear.** The composite
`𝒪_{S,s} ⟶ C ⟶ κ` is the structure map of `κ` over `𝒪_{S,s}`.

Both are local homomorphisms out of the local ring of `S` at `s` into the field `κ`, and both
induce the same morphism `Spec κ ⟶ S` — the first by
`Deformation.Artin.specMap_stalkAlgebra_comp_fromSpecStalk` together with the hypothesis on the
residue point, the second by definition. So
`Deformation.Artin.localHom_fromSpecStalk_injective` identifies them. -/
public theorem residueMap_stalkAlgebra :
    letI := stalkAlgebra iΛ s hloc C hres
    (residueMap C).comp (algebraMap (S.presheaf.stalk s) (C : Type u)) =
      algebraMap (S.presheaf.stalk s) k := by
  let := stalkAlgebra iΛ s hloc C hres
  have := isLocalHom_stalkAlgebra iΛ s hloc C hres
  have := isLocalHom_residueMap C
  have := hloc
  exact comp_eq_of_specMap_comp_fromSpecStalk S s _ _ _
    (specMap_stalkAlgebra_comp_fromSpecStalk iΛ s hloc C hres) hres.symm

end StalkAlgebra

/-! ### The object and the morphism of `𝒞_{𝒪_{S,s}}` -/

section StalkObj

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) (s : S)
  [algStalk : Algebra (S.presheaf.stalk s) k]
  (hloc : IsLocalHom (algebraMap (S.presheaf.stalk s) k))

/-- **An object of `𝒞_Λ` as an object of `𝒞_{𝒪_{S,s}}`.** The carrier, the ring, the Artinian
and local structures and the underlying equivalence of residue fields are reused unchanged;
only the algebra structure is replaced by `Deformation.Artin.stalkAlgebra`, whose compatibility
with the residue identification is `Deformation.Artin.residueMap_stalkAlgebra`. -/
public def stalkObj (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s) :
    ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k where
  carrier := C
  algebra := stalkAlgebra iΛ s hloc C hres
  residueEquiv :=
    letI := stalkAlgebra iΛ s hloc C hres
    { C.residueEquiv with
      commutes' := fun t =>
        RingHom.congr_fun (residueMap_stalkAlgebra iΛ s hloc C hres) t }

/-- The carrier of `Deformation.Artin.stalkObj` is that of its input. -/
public theorem stalkObj_carrier (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s) :
    (stalkObj iΛ s hloc C hres : Type u) = (C : Type u) := rfl

/-- The map to the fixed residue field is unchanged by
`Deformation.Artin.stalkObj`. -/
public theorem residueMap_stalkObj (C : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hres : Spec.map (CommRingCat.ofHom (residueMap C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s) :
    residueMap (stalkObj iΛ s hloc C hres) = residueMap C := rfl

variable (A B : ArtinianLocalAlgCat.{u, u, u} Λ k)
  (hresA : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Λ (A : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s)
  (hresB : Spec.map (CommRingCat.ofHom (residueMap B)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Λ (B : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s)
  (f : B ⟶ A)

/-- A morphism of `𝒞_Λ` commutes with the structure maps from `Λ`, as morphisms of
`CommRingCat`. -/
private theorem ofHom_algebraMap_comp_ofHom_hom :
    CommRingCat.ofHom (algebraMap Λ (B : Type u)) ≫ CommRingCat.ofHom f.hom.toRingHom =
      CommRingCat.ofHom (algebraMap Λ (A : Type u)) := by
  apply CommRingCat.hom_ext
  ext l
  exact f.hom.commutes l

include hloc hresA hresB in
/-- **A morphism of `𝒞_Λ` is automatically `𝒪_{S,s}`-linear.** Both `f ∘ (𝒪_{S,s} ⟶ B)` and
`𝒪_{S,s} ⟶ A` are local homomorphisms into `A` inducing the same morphism `Spec A ⟶ S`, the
first because `f` is `Λ`-linear, so
`Deformation.Artin.localHom_fromSpecStalk_injective` identifies them. -/
public theorem hom_comp_stalkAlgebra :
    letI := stalkAlgebra iΛ s hloc A hresA
    letI := stalkAlgebra iΛ s hloc B hresB
    f.hom.toRingHom.comp (algebraMap (S.presheaf.stalk s) (B : Type u)) =
      algebraMap (S.presheaf.stalk s) (A : Type u) := by
  let := stalkAlgebra iΛ s hloc A hresA
  let := stalkAlgebra iΛ s hloc B hresB
  have := isLocalHom_stalkAlgebra iΛ s hloc A hresA
  have := isLocalHom_stalkAlgebra iΛ s hloc B hresB
  have := f.isLocal
  refine comp_eq_of_specMap_comp_fromSpecStalk S s _ _ _
    (specMap_stalkAlgebra_comp_fromSpecStalk iΛ s hloc B hresB) ?_
  rw [specMap_stalkAlgebra_comp_fromSpecStalk iΛ s hloc A hresA, ← Category.assoc,
    ← Spec.map_comp, ofHom_algebraMap_comp_ofHom_hom A B f]

include hloc hresA hresB in
/-- **A morphism of `𝒞_Λ` as a morphism of `𝒞_{𝒪_{S,s}}`**, with the same underlying ring
map. -/
public def stalkHom : stalkObj iΛ s hloc B hresB ⟶ stalkObj iΛ s hloc A hresA where
  hom :=
    letI := stalkAlgebra iΛ s hloc A hresA
    letI := stalkAlgebra iΛ s hloc B hresB
    { toRingHom := f.hom.toRingHom
      commutes' := fun t =>
        RingHom.congr_fun (hom_comp_stalkAlgebra iΛ s hloc A B hresA hresB f) t }
  isLocal := f.isLocal
  residue_comm := f.residue_comm

include hloc hresA hresB in
/-- The ring map underlying `Deformation.Artin.stalkHom` is the one underlying its input. -/
public theorem stalkHom_hom_toRingHom :
    (stalkHom iΛ s hloc A B hresA hresB f).hom.toRingHom = f.hom.toRingHom := rfl

end StalkObj

/-! ### The transfer of the lifting property -/

section ChangeBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) (s : S)
  [algStalk : Algebra (S.presheaf.stalk s) k]
  (hloc : IsLocalHom (algebraMap (S.presheaf.stalk s) k))
  {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
  (U : Over S) (x : X) (hx : q.obj x = U) (κ : Spec (.of k) ⟶ U.left)
  (hκ : κ ≫ U.hom =
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s)

include hloc hκ in
/-- **The change of deformation base.** If the lifting property defining versality holds with
the local ring of `S` at `s` as deformation base, it holds with any `Λ` whose spectrum maps to
`S` compatibly with the chosen residue point.

Every Artinian local `Λ`-algebra occurring in a lifting problem has its residue point at the
chosen point of `S` — for the target because the lifting property already imposes that of the
arrow `a`, read through `Deformation.Artin.schemeMap_over`, and for the source because the
surjection is `Λ`-linear and respects the residue identifications — so each is canonically an
`𝒪_{S,s}`-algebra (`Deformation.Artin.stalkObj`), the surjection between them is a morphism of
`𝒞_{𝒪_{S,s}}` with the same underlying ring map (`Deformation.Artin.stalkHom`), and the two
presentations of each base over `S` agree
(`Deformation.Artin.specMap_stalkAlgebra_comp_fromSpecStalk`).

Nothing is asked of `iΛ`: not that it be an open immersion, nor even a monomorphism. The
factorization through the local ring is produced at the level of schemes, so `𝒪_{S,s}` is never
identified with a localization of `Λ`. -/
@[stacks 07YM "the lifting property over the local ring of S transfers to the affine open"]
public theorem liftsAtResiduePoint_changeBase
    (hstalk : LiftsAtResiduePoint (Λ := S.presheaf.stalk s) (k := k) (alg := algStalk)
      (S.fromSpecStalk s) q U x hx κ) :
    LiftsAtResiduePoint (Λ := Λ) (k := k) iΛ q U x hx κ := by
  intro A B f hf y z hy hz i hi a ha
  -- The residue point of `A`, read through its structure morphism, is the chosen one.
  have hresA : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (A : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s := by
    have hover : schemeMap q hy hx a ≫ U.hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (A : Type u))) ≫ iΛ :=
      schemeMap_over q hy hx a
    rw [← hover, ← Category.assoc, ha, hκ]
  -- The same for `B`: the surjection is `Λ`-linear and respects the residue identifications.
  have hresB : Spec.map (CommRingCat.ofHom (residueMap B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ (B : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s := by
    have hrm : CommRingCat.ofHom (residueMap B) =
        CommRingCat.ofHom f.hom.toRingHom ≫ CommRingCat.ofHom (residueMap A) := by
      apply CommRingCat.hom_ext
      ext b
      exact (f.residue_comm b).symm
    rw [hrm, Spec.map_comp, Category.assoc, ← Category.assoc
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom)), ← Spec.map_comp,
      ofHom_algebraMap_comp_ofHom_hom A B f]
    exact hresA
  -- The two bases, presented over the local ring of `S`.
  have hy' : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) ((stalkObj iΛ s hloc A hresA : Type u)))) ≫
        S.fromSpecStalk s) := by
    rw [hy]
    exact congrArg Over.mk (specMap_stalkAlgebra_comp_fromSpecStalk iΛ s hloc A hresA).symm
  have hz' : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) ((stalkObj iΛ s hloc B hresB : Type u)))) ≫
        S.fromSpecStalk s) := by
    rw [hz]
    exact congrArg Over.mk (specMap_stalkAlgebra_comp_fromSpecStalk iΛ s hloc B hresB).symm
  exact hstalk (stalkObj iΛ s hloc A hresA) (stalkObj iΛ s hloc B hresB)
    (stalkHom iΛ s hloc A B hresA hresB f) hf y z hy' hz' i hi a ha

end ChangeBase

/-! ### Versality read with an arbitrary affine deformation base -/

section VersalChangeBase

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
  (U : Over S) {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
  (u₀ : U.left) (x : X) (hx : q.obj x = U)
  [Algebra Λ (U.left.residueField u₀)]

include hx in
/-- **Versality at a point, read with an arbitrary affine deformation base.** If `x` is versal
at `u₀` then the lifting property holds with *any* `Spec Λ ⟶ S` as deformation base, at the
canonical residue-field point of `u₀`.

`Deformation.Artin.IsVersalAt` is literally the lifting property with the local ring of `S` at
the image of `u₀` as base (`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`), and
`Deformation.Artin.liftsAtResiduePoint_changeBase` moves the base; the one compatibility it
asks of the residue point is that it factor through that local ring, which is
`AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk`.

This is the form the degree `-1` half of the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM]
consumes: the small extension it tests versality against is built from `Λ`-algebras, `Λ` being
the ring of the affine open the family maps into, and the objects of `𝒞_{𝒪_{S,s}}` are not
available to it. Nothing is asked of `iΛ` — in particular not that it be an open immersion. -/
@[stacks 07YM "versality gives the lifting property over any affine deformation base"]
public theorem liftsAtResiduePoint_base_of_isVersalAt
    (hversal : IsVersalAt U q u₀ x hx) :
    LiftsAtResiduePoint (Λ := Λ) (k := U.left.residueField u₀) iΛ q U x hx
      (U.left.fromSpecResidueField u₀) :=
  let algStalk := residueFieldAlgebra U u₀
  have hloc : IsLocalHom
      (algebraMap (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀)) :=
    show IsLocalHom (Scheme.stalkClosedPointTo (residueFieldBasePoint U u₀)).hom from
      inferInstance
  have hstalk : LiftsAtResiduePoint (Λ := S.presheaf.stalk (basePoint U u₀))
      (k := U.left.residueField u₀) (alg := algStalk)
      (S.fromSpecStalk (basePoint U u₀)) q U x hx (U.left.fromSpecResidueField u₀) :=
    (isVersalAt_iff_liftsAtResiduePoint U q u₀ x hx).mp hversal
  liftsAtResiduePoint_changeBase iΛ (basePoint U u₀) hloc q U x hx
    (U.left.fromSpecResidueField u₀)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (residueFieldBasePoint U u₀)).symm hstalk

end VersalChangeBase

end Deformation.Artin
