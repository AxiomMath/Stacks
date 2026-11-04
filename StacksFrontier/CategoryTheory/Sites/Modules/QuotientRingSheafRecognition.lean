module

public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafEpi

/-!
# Recognising a quotient of a sheaf of rings as the quotient by its kernel

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `α : O ⟶ R` be a *locally
surjective* morphism of sheaves of commutative rings — a quotient of `O`, formed in whatever way
the ambient construction happens to form it. This file identifies `R` with
`Stacks.Sites.quotientRingSheaf` of the ideal of kernels of `α`, compatibly with the two quotient
maps.

Nothing before this recognised a quotient. `Stacks.Sites.quotientRingSheaf` is a construction —
the sheafification of the objectwise quotient — and `Stacks.Sites.cokernelIsoQuotientRing`
compares it with the other construction a sheaf of ideals admits, its cokernel in sheaves of
modules. Both are statements about objects built *from* the ideal. What a consumer with a
quotient already in hand needs is the converse: that a locally surjective morphism out of `O`
whose kernel is `I` *is* `O/I`, so that two quotients of `O` with the same kernel are the same
quotient.

## Main definitions

* `Stacks.Sites.quotientPresheafDesc` and `Stacks.Sites.quotientRingSheafDesc`: the comparison
  `O/I ⟶ R` induced by a morphism `α : O ⟶ R` killing `I` over every object of the site; the
  first is the objectwise map out of the objectwise quotient, the second its extension to the
  sheafification.
* `Stacks.Sites.quotientRingSheafIso`: **the recognition** — for `α` locally surjective whose
  kernel over every object is the ideal of sections of `I` there, the comparison is an
  isomorphism `O/I ≅ R`.

## Main results

* `Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafDesc`: the comparison carries the
  quotient map `O ⟶ O/I` to `α`, so it identifies the quotient *maps* and not merely the two
  objects.
* `Stacks.Sites.isLocallySurjective_quotientRingSheafDesc` and
  `Stacks.Sites.isLocallyInjective_quotientRingSheafDesc`: the comparison is locally surjective
  as soon as `α` is, and locally injective as soon as the kernel of `α` over every object is
  contained in `I`.
* `Stacks.Sites.isIso_quotientRingSheafDesc`: the comparison is an isomorphism.

## Implementation notes

**Both halves of local bijectivity are proved from local surjectivity of the quotient map.**
A section of `O/I` over an object need not come from a section of `O` there, so neither half can
be checked objectwise; what replaces that is
`Stacks.Sites.isLocallySurjective_toQuotientRingSheaf`, which covers the object by ones over
which the section *is* a class. Local surjectivity of the comparison then comes from local
surjectivity of `α` alone: a local preimage of a section of `R` under `α` is a local preimage
under the comparison, its class being one. Local injectivity is where the kernel hypothesis
enters: two sections of `O/I` with the same image are, on a common refinement, classes of
sections `a` and `b` of `O`, and then `α (a - b) = 0`, so `a - b` lies in the kernel of `α` over
that object, hence in `I`, hence the two classes agree there.

Only the containment `sections of I ⊆ ker α` is used for the comparison to exist, and only the
reverse one for local injectivity; the isomorphism statement therefore takes the equality.

**The kernel hypothesis is stated with `RingHom.ker` and not with
`SheafOfModules.kerIdeal`.** The kernel ideal of a morphism of sheaves of rings is available —
`SheafOfModules.kerIdeal`, whose sections are exactly these kernels by
`SheafOfModules.kerIdeal_obj` — but it is defined for a morphism of `RingCat`-valued sheaves,
whereas the quotient construction is `CommRingCat`-valued, so phrasing the hypothesis through it
would make every consumer cross `CategoryTheory.sheafCompose` before it could state the input at
all. The objectwise form is the one both sides can write down, and
`SheafOfModules.kerIdeal_obj` converts it where the ideal form is wanted.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O R : Sheaf J CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}]
  (α : O ⟶ R) (I : IdealSubsheaf O)

/-- **The objectwise comparison out of the objectwise quotient.** A morphism `α : O ⟶ R` of
sheaves of commutative rings killing the sections of `I` over every object of the site factors
through the objectwise quotient `U ↦ O(U)/I(U)`. -/
def quotientPresheafDesc (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom) :
    quotientPresheaf I ⟶ R.obj where
  app V := CommRingCat.ofHom (Ideal.Quotient.lift (sectionIdeal I V) (α.hom.app V).hom (hI V))
  naturality {V W} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact ConcreteCategory.congr_hom (α.hom.naturality f) a

/-- **The comparison `O/I ⟶ R`** induced by a morphism `α : O ⟶ R` killing the sections of `I`
over every object of the site: the objectwise comparison extended to the sheafification, `R`
being a sheaf. -/
def quotientRingSheafDesc (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom) :
    quotientRingSheaf I ⟶ R :=
  ⟨sheafifyLift J (quotientPresheafDesc α I hI) R.property⟩

/-- **The comparison carries the quotient map `O ⟶ O/I` to `α`**, so it identifies the quotient
*maps* and not merely the two objects. -/
@[reassoc (attr := simp)]
theorem toQuotientRingSheaf_comp_quotientRingSheafDesc
    (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom) :
    toQuotientRingSheaf I ≫ quotientRingSheafDesc α I hI = α := by
  apply Sheaf.hom_ext
  show (toQuotientPresheaf I ≫ toSheafify J (quotientPresheaf I)) ≫
    sheafifyLift J (quotientPresheafDesc α I hI) R.property = α.hom
  rw [Category.assoc, toSheafify_sheafifyLift]
  ext V a
  rfl

/-- The comparison composed with the quotient map is `α`, read on a section. -/
theorem quotientRingSheafDesc_app_apply
    (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom) (V : Cᵒᵖ)
    (a : O.obj.obj V) :
    (quotientRingSheafDesc α I hI).hom.app V ((toQuotientRingSheaf I).hom.app V a) =
      α.hom.app V a :=
  ConcreteCategory.congr_hom
    (congrArg (fun g : O ⟶ R => g.hom.app V)
      (toQuotientRingSheaf_comp_quotientRingSheafDesc α I hI)) a

/-- **The comparison is locally surjective as soon as `α` is.** A local preimage of a section of
`R` under `α` is a local preimage under the comparison: its class is one, the comparison carrying
the quotient map to `α`. -/
instance isLocallySurjective_quotientRingSheafDesc
    (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom)
    [Presheaf.IsLocallySurjective J α.hom] :
    Presheaf.IsLocallySurjective J (quotientRingSheafDesc α I hI).hom where
  imageSieve_mem {V} z := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J α.hom z)
    rintro W g ⟨a, ha⟩
    exact ⟨(toQuotientRingSheaf I).hom.app (op W) a,
      (quotientRingSheafDesc_app_apply α I hI (op W) a).trans ha⟩

/-- **The comparison is locally injective as soon as the kernel of `α` is contained in `I` over
every object.** Two sections of `O/I` with the same image are, on a common refinement, classes of
sections `a` and `b` of `O`; their images under `α` agree there, so `a - b` lies in the kernel of
`α`, hence in `I`, hence the two classes agree — a section of `I` being killed by the quotient
map, which is `Stacks.Sites.app_mem_ker_of_mem`. -/
theorem isLocallyInjective_quotientRingSheafDesc
    (hI : ∀ V : Cᵒᵖ, sectionIdeal I V ≤ RingHom.ker (α.hom.app V).hom)
    (hI' : ∀ V : Cᵒᵖ, RingHom.ker (α.hom.app V).hom ≤ sectionIdeal I V) :
    Presheaf.IsLocallyInjective J (quotientRingSheafDesc α I hI).hom where
  equalizerSieve_mem {V} x y h := by
    have := isLocallySurjective_toQuotientRingSheaf I
    refine J.superset_covering ?_ (J.intersection_covering
      (Presheaf.imageSieve_mem J (toQuotientRingSheaf I).hom x)
      (Presheaf.imageSieve_mem J (toQuotientRingSheaf I).hom y))
    rintro W g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have key : ∀ (c : O.obj.obj (op W)) (z : (quotientRingSheaf I).obj.obj V),
        (toQuotientRingSheaf I).hom.app (op W) c = (quotientRingSheaf I).obj.map g.op z →
        α.hom.app (op W) c =
          R.obj.map g.op ((quotientRingSheafDesc α I hI).hom.app V z) := by
      intro c z hc
      rw [← quotientRingSheafDesc_app_apply α I hI (op W) c, hc]
      exact ConcreteCategory.congr_hom
        ((quotientRingSheafDesc α I hI).hom.naturality g.op) z
    have hab : a - b ∈ RingHom.ker (α.hom.app (op W)).hom := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, key a x ha, key b y hb, h]
    show (quotientRingSheaf I).obj.map g.op x = (quotientRingSheaf I).obj.map g.op y
    rw [← ha, ← hb, ← sub_eq_zero, ← map_sub]
    exact app_mem_ker_of_mem I (op W) (hI' (op W) hab)

variable [Presheaf.IsLocallySurjective J α.hom]

/-- **The comparison is an isomorphism**: a locally surjective morphism out of `O` whose kernel
over every object is the ideal of sections of `I` there exhibits its target as `O/I`. The
comparison is locally surjective and locally injective, and a locally bijective morphism of
sheaves is an isomorphism (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`). -/
theorem isIso_quotientRingSheafDesc
    (hI : ∀ V : Cᵒᵖ, RingHom.ker (α.hom.app V).hom = sectionIdeal I V) :
    IsIso (quotientRingSheafDesc α I fun V => (hI V).ge) :=
  have := isLocallyInjective_quotientRingSheafDesc α I (fun V => (hI V).ge) fun V => (hI V).le
  (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩

/-- **The recognition of a quotient.** A locally surjective morphism `α : O ⟶ R` of sheaves of
commutative rings whose kernel over every object of the site is the ideal of sections of `I`
there identifies `R` with the quotient `O/I`. -/
def quotientRingSheafIso (hI : ∀ V : Cᵒᵖ, RingHom.ker (α.hom.app V).hom = sectionIdeal I V) :
    quotientRingSheaf I ≅ R :=
  haveI := isIso_quotientRingSheafDesc α I hI
  asIso (quotientRingSheafDesc α I fun V => (hI V).ge)

/-- The forward morphism of `quotientRingSheafIso` is `quotientRingSheafDesc`. -/
@[simp] theorem quotientRingSheafIso_hom
    (hI : ∀ V : Cᵒᵖ, RingHom.ker (α.hom.app V).hom = sectionIdeal I V) :
    (quotientRingSheafIso α I hI).hom = quotientRingSheafDesc α I fun V => (hI V).ge :=
  rfl

/-- The recognition carries the quotient map `O ⟶ O/I` to `α`. -/
@[reassoc (attr := simp)]
theorem toQuotientRingSheaf_comp_quotientRingSheafIso_hom
    (hI : ∀ V : Cᵒᵖ, RingHom.ker (α.hom.app V).hom = sectionIdeal I V) :
    toQuotientRingSheaf I ≫ (quotientRingSheafIso α I hI).hom = α :=
  toQuotientRingSheaf_comp_quotientRingSheafDesc α I fun V => (hI V).ge

end Stacks.Sites

end
